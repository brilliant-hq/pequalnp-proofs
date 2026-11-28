import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52986_aux
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

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

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
def goal_90 : Nat := 0xffffffccffffffcccccccc00cccccc00ffffffccffffffcccccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeeeee00eeeeee00ffffffeeffffffeeeeeeee00eeeeee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xffffff00ffffff00f0f00000f0f00000ffffff00ffffff00f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xffffffaaffffffaafafaaa00fafaaa00ffffffaaffffffaafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xffffffccffffffccfcfccc00fcfccc00ffffffccffffffccfcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffffffeeffffffeefefeee00fefeee00ffffffeeffffffeefefeee00fefeee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeeaaaaaaaa00000000ffffffffeeeeeeeeaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xffffffffccccccccf0f0f0f000000000ffffffffccccccccf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffccff00ff00cc00cc00ffffffffffccffccff00ff00cc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffaaffaaee00ee00ffffffffffeeffeeffaaffaaee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xffffffffff00ff00fff0fff000000000ffffffffff00ff00fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaafffafffaaa00aa00ffffffffffaaffaafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xffffffffffccffccfff0fff0cc00cc00ffffffffffccffccfff0fff0cc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaaaaaaaaaa0000ffffffffffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccc0000cccc0000ffffffffffffcccccccc0000cccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffeeeeeeeeaaaaeeee0000ffffffffffffeeeeeeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xffffffffffffccccfcfcf0f0fcfc0000ffffffffffffccccfcfcf0f0fcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xffffffffffffeeeefefefafafefe0000ffffffffffffeeeefefefafafefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff00ff0000000000ffffffffffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffaaffaaaaaaaa00ffffffffffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffffccffccff00cccccc00ffffffffffffffccffccff00cccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffeeffeeffaaeeeeee00ffffffffffffffeeffeeffaaeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xffffffffffffff00fff0fff0f0f00000ffffffffffffff00fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xffffffffffffffccfffcfff0fcfccc00ffffffffffffffccfffcfff0fcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xffffffffffffffeefffefffafefeee00ffffffffffffffeefffefffafefeee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefefe0000fefe0000fefe0000fefe0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafaffffaaaaffffaaaafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcffffccccffffccccfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefeffffeeeeffffeeeefefe0000fefe0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0ffffff00ffffff00f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffaffffffaaffffffaafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcffffffccffffffccfcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffeffffffeeffffffeefefeee00fefeee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefeffffffffeeeeeeeefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccff00ff00cc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffeeffaaffaaee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcffffffffffccffccfff0fff0cc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffeffffffffffeeffeefffafffaee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffffffeeeeeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcffffffffffffccccfcfcf0f0fcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefeffffffffffffeeeefefefafafefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffffccffccff00cccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffffeeffeeffaaeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0ffffffffffffff00fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffaffffffffffffffaafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcffffffffffffffccfffcfff0fcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffeffffffffffffffeefffefffafefeee00
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
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_41
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_41
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
def isoMvS_194:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_41
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
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xa0a0000000000000a0a,8,9)] (by decide +kernel) lowS_74
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
|0=>0x204c1324d1404c12448d30481
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
def isoMvS_83:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_75
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_75
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_75
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_29
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_43
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_29
def isoMvS_106:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_75
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_75
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_43
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_75
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_75
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_75
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_43
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_105
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_75
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_75
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_75
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_75
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_105
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 7:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_105
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_75
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_105
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_75
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
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
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,8,10)] (by decide +kernel) lowS_105
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_slice_b [(0x3030000030300000303000003030,32,36)] (by decide +kernel) lowS_105
namespace S_115
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,18),(2,66),(3,19),(3,35),(3,67),(16,17),(16,18),(16,80),(32,33),(32,96),(34,35),(34,50),(34,98),(48,49),(48,50),(48,112),(64,65),(64,66),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_115.map (·&&&dom_115)
def gM:=goal_115&&&dom_115
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000000f000f00000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000af000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 116 0xfffffffffffffffffffffffffffff
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
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_113 5 roots_113 ops++addP pm 2 dom_99 5 roots_99 ops++addP pm 3 dom_83 5 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_115==dom_115)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_115 gM v ys):RunD true dom_115 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_115 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_115 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,16,17)] (by decide +kernel) lowS_150
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_slice_b [(0xa0a0000000000000a0a0000000000000a0a0000000000000a0a,8,9)] (by decide +kernel) lowS_202
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
def isoMvS_55:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_61:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_93
def isoMvS_110:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_93
def isoMvS_118:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_115
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_115
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_107
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 7:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_115
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_115
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_115
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_115
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_115
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_109
def isoMvS_211:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_203
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_107
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_107
def isoMvS_217:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_203
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_115
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_234:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_203
def isoMvS_241:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_203
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_107
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
|0=>0xecdd9d7ad6e56cd59d4ed49d18010009008406106002001a019014009008005004002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000010000000000
|6,0=>0xa03308703428504230006342de04840a081c000200
|7,0=>0x1194af6a4ed8
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_54 4 roots_54 ops++addP pm 2 dom_47 6 roots_47 ops++addP pm 3 dom_55 5 roots_55 ops++addP pm 4 dom_31 5 roots_31 ops++addP pm 5 dom_45 5 roots_45 ops++addP pm 6 dom_43 5 roots_43 ops++addP pm 7 dom_61 6 roots_61 ops++addP pm 8 dom_29 4 roots_29 ops++addP pm 9 dom_57 5 roots_57 ops++addP pm 10 dom_59 6 roots_59 ops++addP pm 11 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_61 _ g hchk
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
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xf000f000f000f000f000f000f000f0,16,20)] (by decide +kernel) lowS_115
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,40),(32,96),(34,35),(34,42),(34,50),(34,98),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe8a58a01c49ea039af618e65c82bf973a1b733e849cf24760a431a9430c7419ac357d53481f2c78825ee11c8c5195dc0e14b04e44
|5,0=>0xdcd5ad987bd3eb6d2611c2c19bd650bb15bb0f88a96daa8c96a4007a019a9ed419c1af93656925f28e82a85a0f79a30777d76e265599e9598ca592fb546e753c845345b4f5444eea34dc8a4d7a54ced748e9848a3d3c8363a5ea3816336c12361482d3362a52f2932727905260cd25af61dd161dacd1a4f41a09b13c781157c113df1098f0cb860ca120baa909f8f082e806b850619701ab5
|6,0=>0xfb4a3f8cbbef4eada5b4d4264b6172b1360af262aaf1ba983ea928ca8027a770da3a48a0069984aa8e4ea89bec8613084f4881edb800377b0887a9dc73ca870377701d86ec406dd5e6a1f26a05561a7e5eb5d5cf835bcf94a924476a04559143d5340e123f79b3e9973d7cf3a7e1398f6397cc3877434d7334b353376132c932e5162d12e28a5b26a4024d2a23fa6229b51e3fd19c1f181fd174b5163ee14f33140e10c9840b4d80b2e30a27c06f93
|7,0=>0xdbc5cc181abe12db3367b0e768fad88eb9b8db868c8fb8532075a2f6a42d645a06240e60c6f5f86f5be23502e24d87b4ca6c4b6d0496ca475b7413873b21c391043655835e912f28f2cd922c9172a1ee2816a240591ffcd1fafa1ee0e1d48e151231489e0c68209d3b07721025fa019e0
|8,0=>0xfc7cde05f3cdd925459947c68450bc32d0c15bd40e7a107721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0c0c0c0c0c0c0c0c0cf0f0f0e0f0f0f0e0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f000f0f0f00f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0a0a0a0a0a0a0a0a0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a000000f0000000f0000000e0000000ef0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f000f000f000f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0eb0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a
|0,1=>0xf0f0f000f0f0f000e0e0e000e0e0e00f0f0f0f0f0f0e0e0f0f00000f0f0000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0a0f0f0f0a0f0f0f0a0f0a0f0a0f0ae0e0e0e0e0e0e0e0e0e0e000e0e0e00f0f0f0f0f0f0f0a0f0f0f0f00000000f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a00000000f0f0f0f000000000f0a0f0af0f0f0f0f0e0f0e0f0f0f0f00000000f0f0f0a0f0f0f0a0f000f000f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af000f0f0f000f0f0f000f0a0f000f0af0f00000f0f00000f0f00000f0f0000f0f0f0f0e0e0e0e0a0a0a0a0a0a0a0a50505050505050505040504050405040000000000000000f0f0f0a0f0f0f0a
|0,2=>0xf010f010f010f010f000f000f000f001010101010101010000000000000000f0f0f0a0f0f0f0a0000000000000000b0b0b0b0b0b0b0b0b0b0b0a0b0b0b0af0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0e0f0e0f0e0f0e0000000000000000a0a0a0a0b0b0b0b0a0a0a0a0a0a0a0a303030303030303030303000303030000f000f00000000000f000f00000000f0f0f0f0f0f0f0000000000000000003030300030303030303030003030300f0f0f0f010101010f0f0f0f00000000505050500000000050505050000000000000000f0f0f0f000000000f0e0f0e3030301030303010303030003030300f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a
|0,3=>0xf000f000f000f000f000f000e000e0000000000000000f0f0f0f0e0e0e0e00000000f0f0f0f000000000f0f0f00b0b0b0b0b0b0b0b0b0a0b0a0b0a0b0af0f0f0f0f0f0f000f0f0f0f0f0f0f000000000000000000f0e0f0e0f0e0f0e1010101010101010100010001000100000000f0000000f000000000000000050505050505050505050505040404041010101010101010101010100000000b0b0b0b0b0b0b0b0b0b0b0b0a0a0a0af0f0f0f0e0e0e0e0f0f0f0f0e0e0e0ef0f0f0f0f0f0f0f0f0e0f0e0f0e0f0ef000f0f0f000f0f0f000f000f000f00f000f050f000f050f000f000f000f005050505050505050505050005050500
|0,4=>0xf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f000f000f00000000505050505050505050005000500050000f000f000f000f0000000000000000000000f0000000f0000000a0000000af0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e000000f0000000f0000000f000000000000000010101010000000000000000f0b0f0b0f0b0f0b0f0a0f0a0f0a0f0a00f000f0000000f000f000f000000000000f0f00000f0f00000e0e00000e0ef0f0f0f0f0e0f0e0f000f000f000f00f0f0f0e0f0f0f0e0f0f00000f0f00003030303030303030303030303030300f000f000f0f0f0f0f000f000f0f0f000000f0f00000f0f00000f0e00000f0e
|0,5=>0xf0f0f0f0000000f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f00000000e0f0e0f0e0f0e0f0e0e0e0e0e0e0e0ef0f0f0f000000000000000000000000f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0000005000000050000000000000000505050505050505050505050000000000f000f000f000f000e000e000e000ef0f0f0f0f0f0f0f0f0f0f0f0f000f0000f000f000f000f000f000f00000000e0e0e0e0f0f0f0f0e0e0e0e0e0e0e0e5050505050505050000000000000000f050f050f050f050f000f000f000f0000000000f0f0f0f0000000000000000f000f000f0f0f0f0f000f000f000f00f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a
|0,6=>0x50505050000000000000000f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c00000000f000f000f000f000f000f00005000500050005000000000000000000000000f0f0f0f000000000f000f00f0f0f0f050505050f0f0f0f00000000a0a0a0a0f0f0f0f00000000000000000000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0ef0f0f0f0f000f000f0f0f0f0f000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x26280920a10182025429314046a20a1018a1a842844028d85081c09f0a10f0a3a3420304386840608488080ce010a1018a3654d0304246833204c052e4c1011a101961254203280428c2628092080c0910a108030404203043c684162870d180c509101058a122020702182840608080
|1=>0x30142030e74085080c38960142035e04685084d5823a342032c24685080d5812a14203320428426280910a101870215704060848d5a10f0a0234284062960d0a10982023550c062848d4c1098a02a428406354270a1058a123530406286a50a1019902542841404f8d0a9098a028c284
|2=>0x84c5012a0c48d4ef428426280bc0a10182123530414046860a109ba1404a8406e808d0a1018a0200284402c5010a101811ae4284400c1092a101871255c040608095084c5016e14203047408d084c5016a15a0c2628095080d9811a142036424a8d080d8891a1420304046ae2664501
|3=>0xad02131404a85092818a0234284062848d9214213140468590ec6031424685761058a1234284271c5010a101891b18284261c11d021038a0314284271008d0a1218a0234284261d7810a0c1091a6028406286c20a1058a1235684070448d0a105011b0028426046bf0a5c98a02342be
|4=>0x1234284062808d0ae280c2628495080c50d501421332085010a3020304246859e1098a025428406246ce0a1098214046ae084c38a3a0428426bc5011a1420b06286a80a101891b342842628095981098a3a046cc084d58a025428426645010a101b21234284261c5010ab820314246cb
|5=>0x80c3810a1018a12342da084c5011a15504062848d7a142031235385704c5092a34c05a03098a136428426e85011a142035604685084c5011b6028406246d60b5c2131236b05084c38212542130428095084c5550234284260851d0234203a624685084d98a0234284060808d0a101d1
|6=>0x1a14203320848d0a1098a3a05185c0309821234284061c4950a110031424a85be1018a1234293322848d3014203147408d0a32f131424684262ae811a1420304246d2084c5092b6428c26284db262848d30142135628e8d0a30203042468c084c5092b65f04262808d0a101821254685
|7=>0xb8898a123690c084c10a1234284160c5091a1680c262848d0a1098a1236705761018a123428406284951a1421314246cd0a101891a9c284262808d0b30604262848d0b902131424685084c5091a171de262848d084c382125428c080c48dac1420314246854c3098a028c2e1084c501
|8=>0x14246d90a1098714042cf181098a1234284279c48d0a1098a12342e6084d58a023428426284db0a1098a1237285ae109821424685084c5092a3690c262848d461421314246d60a302131424a8d181098a1236a0c262848db8109d31424685ae1098a1234284261c1091a14213a22848d
|9=>0xa1098a12342d4a01098a1234284262848d0b482131404685181098a1234284062808d0a1098a02342d2c010982123428c084c5011a1421304284951a1098a12546cc080c1091a142031424685701098a12342e9084cc8a1234284262b40d0a109991424a8d0a109821424a8d0a30213
|10=>0x84c5091a142131424685b8131131424685084c38a1234284262848d46142131424a8d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8deb1b76362c6ad8d2b19f6332c64d8c6b1876302c5ed8bab16f62d2c58d8aeb15762a2c52d8a2b13f6272c4d149731286244c47188b31106214c41187f30f861e4c3b187330e061b4c355467b0c96186c2f585bb0b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6eeedc1db4bb6366b8ed55da73b477682cce9d9a332d7650ac8998dbb15661cec1dd803afb55e8ebb5d733adf75b0eb45d653ac4657aeadd9583aaa6548ca75d4b3a906512ea0d93eb27674e0c9a9931ba5c74aae93d9243a417474e8cdd16b2276440e865d09b20d640ce7fdcfc39f173d4e78dcee39d57
|6,1=>0x1d02b997724ee2ddc2b37e7
|7,0=>0x4d769a0f325e613cbb7968f2b9a53bca07932f24da45c48388f711d5a36c46768c0f165e29b44c788910f5e1b3c2f7850f085e0db414781af019dffbbf967e30fa9df1bbdc77aaef39de3bbc16774eecddd63ba57
|8,0=>0x28dbd147a1af419e7fbcf879e2f3a9e7234dd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 106 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1a151416123512351a1512350e151435123514e106162629021612351a15060526290815080d0615080d262902160215141512354014020a761456171a1526291ad918070815081508050405141512350e1526290215141512351a15262926290e1526290216123540145614123506740215123514152629061626290e152a0f
|1=>0x12352629182b0815ae2b182908151a1514151a2914151a15123503490816123502151415123515511a1626290209141512351415123526291549081626291235061626291a150835081516270615262912351a0914152629141508151a1512354e15082b26290216123502151435123514b90216162706152629043714152629
|2=>0x12350829081526291a1514351a1508e106160e150215262912351973081408150331141612351415081626291a151837081508151b71081408660e1514350215123526291415081518370815681708051a1514152629143526291235561414051235082e0615061626290866145518370815561714050229123526293a2b0215
|3=>0x182b08151a1508151a1608150814081515511a161829081514151a2915490816081708161415081506152629083508154e15082b080d26291a1526291a0a1415082b2629141612350949081609511a1646160837c549081708161a1514151a292629182b08157614080d26290815083712356815080512352629141502150837
|4=>0x8140817143508371a151a1608350816123508152629123508161235082914151235081514151a151a1514161415262906162629a01608350e1514351371081414551a1514151a1518370815143512350815157308140e161435140512351b710814080a1415080914151a15081608370815
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x188000000012000000000200000000000000000000000000000
|5,0=>0x291000098c0000000000000000000128800000000000000000002411188000000221000000000021100000000002010e986c830600000000002e2161000000026600008903c80000c30588000000092000000000000000000000c60000000108000000
|6,0=>0x6112fcd7a4ba35c8adc96c2b33581ab4d546a73521a84d3e49c34d126092a692300023cd1a48b244921c90a48233f99f0cf267633999c0cda66a3339990cc265e32d9960caa6523281134c96448323110cc8063d31e08e886e634319100006222f200000005a42a3
|6,1=>0x1a66d03669b28d8e6c43
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a2030e2861428a105062821408a004fe27e13e89f04f627a13c89e04ee27613a89d04e627213889c04de26e13689b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x14080028040033b800667000c56001018002010003400005000009dc00139000261000420000820001000001700002800004c0000800000b0000120000200000210000400000600000800000800000800000800000800000800000
|1=>0x845fe100bdc2013f84026f0804ca1000ac20010830a630614400c198c18110020e67041c4408180810133810a720214ce04198c0823901026f0204ce040880081000101000200c60400800700800267f00240000405000711000c67
|2=>0x1a148234099c681328d02631a04c2340080680058c08501804ca300984600318c002012148e2409dc4813389026512048e240810401368802671004ca2008004002888002d100010200010381358700690c04c61800042813b850269
|3=>0x42022f8000109409a500030a000093804d64000a0780318f002b1e004038098c700100d1265
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x400003000010000000000000000
|5,0=>0x2001c000000000008000000000002080000a0000004000000d024c4800000185000038016680070800006000000000644000044000
|6,0=>0x1daaa8eac09652531bd61818e763ec9e7650364528daa400543472328bbf315612e603c72b12f13929fa50da8d2031023a362d50310440e011250003339
|7,0=>0x3da5969385d1602b69819b79c74fd056faee2c33efdca73ebab86dae5dc7aa7cbceb18cd83768db
|8,0=>0x2edd39597ab9978b5e
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_82 4 roots_82 ops++addP pm 2 dom_90 5 roots_90 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_120 5 roots_120 ops++addP pm 5 dom_115 7 roots_115 ops++addP pm 6 dom_107 8 roots_107 ops++addP pm 7 dom_113 5 roots_113 ops++addP pm 8 dom_57 5 roots_57 ops++addP pm 9 dom_122 7 roots_122 ops++addP pm 10 dom_114 5 roots_114 ops++addP pm 11 dom_58 4 roots_58 ops++addP pm 12 dom_89 5 roots_89 ops++addP pm 13 dom_105 7 roots_105 ops++addP pm 14 dom_97 4 roots_97 ops++addP pm 15 dom_104 4 roots_104 ops++addP pm 16 dom_59 6 roots_59 ops++addP pm 17 dom_51 4 roots_51 ops++addP pm 18 dom_83 5 roots_83 ops++addP pm 19 dom_91 6 roots_91 ops++addP pm 20 dom_75 5 roots_75 ops++addP pm 21 dom_43 5 roots_43 ops++addP pm 22 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
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
def dzo_90_4:=0x505050500000000050505050
def gzo_90_4:=0x505050400000000050504000
def gsh_90_4:=0x50505040000000005050400
theorem lowS_zo_90_4_74:Lower true dzo_90_4 roots_90 gzo_90_4 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_4) [(dom_90,4)] (by decide +kernel) (lower_slice_b (T:=gsh_90_4) [(0x50500000000000005050000,0,16)] (by decide +kernel) lowS_74)
def dzo_74_4:=0x50500000000000005050
def gzo_74_4:=0x50400000000000004000
def gsh_74_4:=0x5040000000000000400
theorem lowS_zo_74_4_74:Lower true dzo_74_4 roots_74 gzo_74_4 4:=lower_iso_b (d1:=dom_74) (r1:=roots_74) (T1:=gsh_74_4) [(dom_74,4)] (by decide +kernel) (lower_slice_b (T:=gsh_74_4) [] (by decide +kernel) lowS_74)
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050405050505050504000
def gsh_122_4:=0x5050505050505040505050505050400
theorem lowS_zo_122_4_74:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16),(0x5050505000000000505050500000000,0,32)] (by decide +kernel) lowS_74)
def dzo_106_4:=0x5050000050500000505000005050
def gzo_106_4:=0x5050000050400000505000004000
def gsh_106_4:=0x505000005040000050500000400
theorem lowS_zo_106_4_74:Lower true dzo_106_4 roots_106 gzo_106_4 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_4) [(dom_106,4)] (by decide +kernel) (lower_slice_b (T:=gsh_106_4) [(0x505000000000000050500000000,0,32)] (by decide +kernel) lowS_74)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(4,20),(4,36),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,18),(16,20),(16,80),(24,26),(24,28),(24,56),(24,88),(32,36),(32,40),(32,96),(34,38),(34,42),(34,50),(34,98),(48,50),(48,52),(48,56),(48,112),(64,66),(64,72),(64,80),(64,96),(68,70),(68,76),(68,84),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfec93e213fca025981826ff284ef292bd191d8751c46719e6a0d8db
|5,0=>0xedae3dfb2adea9fd5951ca97ec8608c26f9c1f5bc0d2cafd49af07cae62bac052a029f9f0789ce859a91698571982899528b94378932ca90b858ad9388e4e881ed85a0584cf9842b9840ae80fbc7fad27edbe7cf777bb6978372731ed6cafb6a2e165813600d75f1f45e3955d72b5d6965a0b957354571a955dae5422e54184539f15343c494e045d9444b5d436b941d183f1b03d4ec3a26139a7039a14368823582734a573415f337fd332472fc8d2f3242c3782bf1d29f4f298c32933028b1525f7520c6020ba91ed671ec5b1d0171cada1a01117fec16a4012d5b116b5108ce101b50eb8f0a09006021046b200de8
|6,0=>0x3912c38e2d38bd538b7d38591384d838311380f137f30378cc3450b3368b333d133247330883279530ae3306b92f87e2ecd52e8d72e8822e2262d27f2d2492cf5b2cea72c9442c3bf2c0d52bf1d2b7c02b2c62a6e32a080295a228c2627b9827b56275642714026b252578a254c625348252b524bb62459723f0523b1f23990237d62332021eaf204ec202271f83a1f0ed1e5041dd721b77919b5518bfa17188162321609015c1415b3315a27159b11526e140de13dc113cf81333413167126e91213211f4011d3e1127610e6110b270fc0e0f57b0f3a40ed9e0e6040db550db1c0ce150c70b0c3b20c2c70bbd60adef0a89a0a5710a09009d8809afd09348085bc0848c079f7075d506e4406b2106a5f0633e05fd905fd805d8a056ff052340423203b1c0373f028800234d020dc01e030155c00e0900d6e009e0008fe0003f
|6,1=>0xb4e97b3298b1db7af993af809af044ae5e3ae3b1ae344ae1a6abf7fa94fba909aa6f1fa3fd4a328ca2437a18dc9da529d74a9c11a99ce5997e898571964df93f5a91fe091b85906d78ff668f52b8f0008b7758882087c398715386811857ef856778486f8417a8364d81b1f81180803c87ff167eec37e4697e2d47c1c87971376e0776b897653676142754d174b72730e77193671619714de70f4170ddc709f9708dc703476f8b76f8076f1316dfc86c98e6ac8e6aaf169b36696aa690456867567d6f67032657ab654d161f126161460cb75f6f15e9c25b6465b0735a8a059df85887557eb455892547e853b7e52df852da0529b2515b750d334fe874fd1d4ef254ec764e66b4de4e4dce14dbb64bc164af364abbf4a7974930e4910348e0d44bd544559435844226e3fce93bc2d3b6533b5b93b4ed3a8bf39f6f39a7039620
|6,2=>0xffb57f3fd5f104cf0305edae3e39bbe2ae1def6adce8bdba4ddb587dabc2d7ca9d562dcf6b8cc1fdca320c94f1c882fc68b8c32fec303dc290bbefe9bce11bcdfabcd98bc43fba31eb6727
|7,0=>0xe2965e14d2e09eeddc2bdbd50d59c9ce680cbe63c63cabf8d3bbb66ba2a0b6dedb2b4eb2965a86b2a6469a5da0a58b1a071b9cda69396e932349294991b8591b0690d7f8f7988bf738be6a88f7c88cf6876ae85b4f834038322182d4c81d8e80d6f80a7f7ea7a7a806757a67500c7247c6fb626efdf6dfc86dcde6ac8e6ac1c69d3068a9d6810b6806f665665f20d5e57f5e4d45d68c5cadb5b9035a44459bdd598d25728755065544ac541f0540765374b52da04fb6b4f6804d8554ca5d4829c44de742e4138dd637fa73600c358d834032331bf330f7320ae318fa3047e300f52edba2e9f22e5742d6032bc092b2a32867f2555624c08239902396d2391122a00224b021b0521aea20bcd1ed7c1c4391ae0618c081811915e29140de12ebf117d60f79e0d1e10c9350a4460a4390a0c30649004f0e048a3044e0036ba01539
|7,1=>0xf0661eb02b
|8,0=>0xe9649e68dbe2965c8943b803badceb7e99577c6d524f44f5f6464f44457d438933c5653188f25b0e1ff1e00935
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x228822882288228822882288228822895555555400000001555555540000000000000000000000008a208a208a208a255555555444444445555555544444444aa88aa88aa88aa88aa88aa880000000154015401540154015401540154015402aaaaaaaaaaaaaaaa82828282828282855555555555555555555555500000000aaaa0000aaaa0000aaaa0000aaaa000155115511551155115511551155115512aaaaaaaa22222222a802a802200220055555555555500005555555555550000aaaaaa00aaaaaa00aaaaaa000000000155555555555555555401540154015402828282828282828282828282828282844444444444444444444444444444444
|0,1=>0xaaaaaaaa00000000aaa8aaa95555555555555555551155115511551220022002200220022002200220022001155115511551155114411441144114488888888888888888888880088888801555511555555115541410141414101400002a8000002a8000002a8000002a80551155115511551155115500551155002200220022002200220022002200220000000000000000015511551155115512aaaaaaaaaaaa2222aaaaa802aaaa20055555500444444005555550044444400aaaaaaaaaaaaaaaa000000000000000155555555540154015555555554015402aaaaaaaaaaaaaaaa22222222222222255555555555555555450545054505450
|0,2=>0xaaaaaaaaaaaaaaaa228822882288228955555401555554015555540155555402aaaa2222aaaa2222aaaa2222aaaa2220000005500000000111111550000000000000000aaaaaaaa000000008888888955555555555555551001100110011002a802a8000002a802a802a800000220044444444444444444444000044444400aaaa8888aaaa8888aaaa8800aaaa88015555555555555554000000011111111000000000000000000002aa200002aa20044004400440044114411441144114488888888888888888888888888008801540154015401540154015401100110000000000000000002a802a802aa22aa254505450545054505450555054505550
|0,3=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a8a0a955555555555555100000000000000002aaa88802aaa88802aaa88802aaa88801111111111111111111100001111000000aa00aa000000aa00aa00aa000000895555555555555555414141414151415002a802a802a802a802a802a80000000004400440044004400440044004400440000000000000000aaaaaa88aaaaaa8800000001551155100000000155115512aaaaa802aaaaa80222222002222220055555555555555555555550055555500aaaaaaaa88888888aaaaaaaa8800880155555511555555115555551155555512aaaaaaaaaaaaaaaaaaa80002aaa800055555555440044005555555544044404
|0,4=>0xaa88aa88aa88aa88aa888888aa88888844444444444444444444000044444402aaa80002aaa80002aaaaa802aaaaa8055555555555555555050555050505550aaaaaaaaa8a8a8a8aaa0aaa0a8a0a8a0000141540001415400014150000141528282828282aa82aa8282828282a282a111111001111110011111100111111002222222222222222222222222222220155555555555555540040004000400040888888888888888888888800888888055555555554455445555555555445544aaaaaaaa00000000aaaaaaaaaa88aa8955555555555555554141414040404042a802a802aa22aa22a802a802aa22aa200550055005500550055000000550000
|0,5=>0x888888880000000088888888000000000110011000000000011001100000000000000002aaaaaaaaaa22aa25555555555555555550055445500554400008888aa00aa8800008888aa00aa8801540154011001100154015401100112222222222222222222222222222220055555555005500555555000000550000aaaaaaaaaaaaaaaa8a008a008a008a0155555555555554015555555555555400000000000000000222222222aa22aa2555555555555555555555555444444440000000000000000aaaaaaaaaaaaaa880000000154015400000000015401540222222222aa22aa2222222222aa22aa200550055005500550055005500440044
|0,6=>0xa2a2a2a2a2a2a2a2a200a200a200a20141414141515151514141414151515152a802a802a802a80220022002200220000550000005500001155000011550000aa00aaaaaa00aaaaaa00aa88aa00aa8844444444444444444444444400000000000000000002aaa8000000000002a8055555555555555551111110011111100aaaaaaaaaaaaaaaaaa00aa00aa88aa8800011110000111100001111000011112a802aa22a802aa22a802aa22a802aa204040404040404040404040404040404aa08aa08aa08aa08aa08aa08aa08aa0955555554011001115555555401100112aaaaaaa88888888aaaaaaaa8888800055550055555500555555004455550044
|0,7=>0xaaaaaaaa00000000aaaaaaaa008800880044004400440044004000400040004000000000000000000002a8000002a8050505050505050505050555050505550aaaaaaaa00008888aaaaaaaa00008888000155100001551000015510000155108aa800008aa800008aa800008aa800011111111111111111110111011101110aaaaaaaaaaaaaaaa000088880000888800000000000000011111111001100110000000000000000002200220022002200000000550055000000000055445544aa22aa22aa22aa22aa22aa220000000000000001555555540000000155555400282828282828000028282828282800055555555555555445555555555555544
|0,8=>0xaaaaaaaaaaaa8888aaaaaaaaaaaa8888000000000001551000000000000155100002aaa80002aaa80002aa200002aa20055005500550055005500550055000000000000aa00aa0088888888aa88aa8911111111111111111001100110011002a2a2a2a2a2a2a2a2a282a282a282a2855555555555555550505050505050000aaaaaaaaaaaaaaaaaaaa8888aaaa8889555555555555555444004400440044022222aa222222aa222222aa222222aa20000000000000000550055005500550000002200000022000000220000002201555555555555555555555555540154000000000002a802a80000000002a800055555555555555550000550000005500
|0,9=>0xaaaa0000888911115555111155551111551111115512aaaaaaaa20022002aaaaaaaa2002200005500550055005500500050005000508800880088008800880888088808880941414141555555554141414151515152aaaaaaa800000002aaaaaaaa222222200000000000000005500554455005544000000aa000000aa000000aa000000011001100110011001100110011111111002a802a802a802a802a8022002a80225500110055001100550011005500110000000000000000002222220022222200000155540001555400015554000154008800880088008800a800a800a800a8000000000550055440000000055005544
|0,10=>0xaa00aa00aa00aa0088008800880089555555555555555555555554000111128282828282828282828002828280028000000005555555500000000555500000000222200002222000022000000220000015554000111100001555400011112a802aaaaa802aa22a802aaaaa802aa25050505000000000505050501010101088aa88aa88aa88aa88a888a888a888a80000000000000000000000011111111000000002aaaaaaa800000002a802a80454545454545454545444544454445440000000000000000888888888888888955555555555555555555555555115512aaaaaaaaaaaaaaa800000002a802a8055555555555555550000000055555500
|0,11=>0x8888888888888888888888880000000041404140414041404140414041404142aaaaaaaaaaaaaaa882808280828082855115511551155115010501050105010aaaaaaaaaaaaaaaaaa002200aa00220155555555555555555555555401100112aaa802aaaaa802aa82800282828002844444444444444445544554455445544aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a800015554000155540001515000015152aaaaaaaaaaaaaaaaaa82aa82aa82aa80000000055555555000000005550555000aa00aa00aa008800aa00aa00aa008844440000444400004554000045540002aaaaaaaaaaaaaaa820202020202020255555555555555555555555555554444
|0,12=>0xaaaaaaaa22222222aa00aa0022002201414141414141414155515551555155500000000000000002aaaaa802aaaaa8000005555000055550000555500000000aa00aaaaaa00aaaaaa00aaaaaa00aa01555155515551555155515551555155500000000000000002aaa2aaa2aaa2aaa454445444544454445444544454445440a000a000a000a000a000a000a000a0155555555555555551511151115111512aaaaaaaaaaaaaaa80002aa200002aa250505050101010105050505010101010aa22aa22aa22aa22aa22aa22aa00aa0154015401540154015555555555115512a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a11111111111111111100110011001100
|0,13=>0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0000155555554015401555555555401100112aaaaaaaaa802aa22aaaaaaaaa802aa255555555555555550000110000001100aaaa8888aaaa8888aaaaaa88aaaaaa8814141414141414141410141014101412222222222222222202020202020202055445544554455445540554055405540000000aa00000088000000aa000000895555555555555555555155515551555282aa82aa82aa82aa82a282a282a282a00005555000055550000550000005500aaaaaaaa0000aaaaaaaaaaaa0000aa0141414541414145414141454141414542a802a802a802a802a802a802aa22aa255550000555555555555000055555500
|0,14=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaa000154015401540154015511551155115510000002a8000002a800000220000002255555555000000005555555555555500aaaa0a00aaaa0a00aaaa0a00aaaa0a01555555540001551155555554000155100000000000000000000088000000880101010101010101010501050105010500a080a080a080a080a080a080a080a095555555555555554141014101410141000000002aaaaaa2000000002aaaaaa2555511115555111155551111555500000000000000000000aa08aa08aa08aa0800000000000000015555555511111112aa22aa22aa22aa2282028202820282050505050505000005050505050500000
|0,15=>0xaaaaaaaa08080808aaaaaaaa080808094141554141415541414155414141554282a8000282a8000282a8000282a800011111111111111111010101010101010aaaaaaaaaaaaaaaa0a000a000a000a01554155415541554155415541554155400002aaa80002aaa800022220000222200110011001100110011001100000000aaaaaaaa00aa00aa888888880088008800000000000000015555555555555402a282a282a282a282a282a282a282a284444444400000000444444440044004422aa22aa22aa22aa20a020a020a020a154015401555555555401540155555402aaa802aaaaa80222aaa802aaaaa802200000000000000000504050405040504
|1,0=>0x22aa22aa22aa22aa00000000000000015555100155551001555510015555100028282828282828282020202020202025555555550505050555555555050505022aa22aa0000000022aa22aa0000000111111110011001111111111001100110000000000000000282828282828282855005500550055001100110011001100
|_,_=>0
def sP:Nat→Nat
|0=>0x30100703028120e0a8280200098380e2105024000e0382840000981c14010007c260e0a01c0c01098301c070b028120e03818021c098380e0a0086c260e038283400098380e1604800320e038600217098380e160483c1c150500422040a01802130901c0a01088380e06080341c070483c1a0c0382c04010701c0c09068300e0b050241007030140204018080200
|1=>0x3878020f09838643105024000e0382c0401000c00e0a04800260e03818022f098385c2d01004220e03858140900010280a00800260705004002c098380e0601004560e03818022a0701c52010004c18080381804010701c14011404c1c2705004220e0382c1409000380e0a02804220e038180401130380e0a048004a0e038180224098300e0a0088c26080701c4409
|2=>0x5004220e039040401088380e160083c2604018280200098380e06048a81c2d0500422400701c143f0004c080c1701802130701c1401000f81c3d0500478130700c0e02008001c070f018022a020205c02008001c070080076130701c143a0004c1807008e470130701c120f098386e0705024000e0380802111b0385a0a008d4260e1a01c0c01088cc0e0a00800260e
|3=>0x38880200098380e0a00938260e268c41409000387a3105024000e1881c144c000380e4b05000260e05004004a098380e0a24800260e170c412000b838620a04800900e038280247098380e0a048008c08038280a01000386207050248a0e03818020d098300e0b05004260e038182c01151101c070100422430701c1409000201c0705108000e038045e0f098386431
|4=>0x60380e0601004260e0397014010004c1c070300802110701c0c090784c080a00800b6130701c0c011a84c1c0703058121d0701c0c01150341c0700920b4130701c14012c84c08580500400130701c0c10150380e0a0495c000e038041e0d09958100701004000e03828125500048a8070100400530701c1401000380e0200944220e038040050098385c4f008002604
|5=>0x1c426700701c14010004c1c07051bc0200098380e02051b800130702802003604c1c07358280200098380e1e030043a130701c040a00800d40e0382802003484c1c07050040068098380e670500400130701cca0a04800260e0398c04010004cc408038280200099841c07050040013071800e0a00800260e0387814012f84c1c0705004225e099741c07050040013
|6=>0x3d8380e0a00844260e1701c14010d84c0854038280200098380e0a00844f4130702812003c84c1c07050040078098101c0a00800ee130701c1401001d8260c0701c14013a84c1c07050043613070b80e090005c26080701c1409000e01c07050240048098380e0a00800e8130701ce60a00800260c0382802001b04c1c072c0280200098380e0a00800e4130701c1411
|7=>0x20300e0a00844260e0381814090004c1c07110042200098380e6542004001302028020033148260e0382812004184c1c07030081401088380e650100400130701c020f099501c07030280213070b80e01001682682040380e0a048001c07050040081098380e0a26000267f0701c14010004c1c07030243a130701c0c0108864260e0382812003f04c1c07051f00013
|8=>0x401c1409000380e0a008011c13220200e0a0080026330701c14010004c1c0705004008d098380e0a0080118130701c140145800260e038291200098380e0a00220260e1721c14010004c1c3103828f800098380e020080090130701c1401088010c041882802002904c1c3103828021b098387a070502400130701c14014284426560601c14010004c1c0705040002a
|9=>0x4b04c1c07050040095098380e060b0043a130701c3c1605004000e0382928090004c1c07050040093099501c070102802000701c140100248260e0382812004884c1c07050040023098380e1605004be13070f40e0200800260e0382802002d84c1c07050040090098380e020084400190701c140108a291e0e188280200098201c070302812000701c0c02008002612
|10=>0x480024080380802000701c14015200026440701c14015184c180e03808140108a881c070500400130701c140108801420e0382802005004c1c0705004009f098380e0a00a7800134e81c14090004c1c0705024009b098380e0a4d00026124c81c14010004c1c074c0280200098380e0a008012e130701cca0a00844260e03818022a070b80c01001e8260e038280200
|11=>0x98301c07050055e130401c1401002a8260e038581401088006607050040013570380e0a00800260e03808021100148100e038040050098380e0a56800260e1702802005604c1c070500400ab098380e024a00400130701d520a00800260e0380814012284c1c07052a000130701c140153800260e0381814015304c08070500400a5098201c070300802000701c2c0a
|12=>0x380400391c04cac0e188280200098385c07008010c130701c14bb0080026ba0701c14010004c180e03878140109a64100705004001302038140108998260e038297200098100e0a009440013070b80eb800800260e1881c14ad0004c1c0a008016c13038081401002d0260e0382802005984c1c0a0080164130701c040a0080162b00701c14010004c1c07050040035
|13=>0x138280200098380e0a008018a13060200e0a048001c07051080013070b85a0a04800260e03b0c14010004d840e038280200098385a070102802110701c14c100b00260c0382802bf098380e0a002f426540701c14010004c180e038040050098101c0a00800f41302038140100100260e0382812bc0004d320e038181401098380e18050040013091ec0e0a00800260e
|14=>0x9839a0070500400132201c1401000d8260e0387814010004cf608038280200098380eb80500400130701c0c0a001c4260e038299e010004c1c2e168080200098380e0a04a9c00130701d9c0a00800260e6681c0c010004c1c07658280200098380e0a048006c13090300e0a00a8c260e03b2414010004c1c07050058c00098101c2e030040013060200e0a008e0260e
|15=>0x801b8130701c0c0a008ac260c0401c0c0a0084c1cdb038280200098380e0a00801b413070500e0a00800260e0388414010004c0808038081401000380ed8050240013478380e0a00844260e0382802006b84c1c076b0280200098380e0a6a8040013698380e0a00800260e03829a400098380e06050044c13060380e0a008f0260e03b4414010004c180e038581401
|16=>0x983010070102802000701c1401088d8260e7201c14010004c1c07718280200098386807008002e13093880e0a00800260e038081401000981c07208281200098380e0b050040013070d00e0a00914260e03818026d098385c2d0500422130701c140170800260e03829be0009b781c070500400130701c14016019026dd0701c14010004c1c07050040025098380e0a
|17=>0x701c14010004c880e038080200098380e0605024be130700c0e0a008002604040b814010004c1c070500400e9098380e0a003a0260c070b80e060084c1c070500400e6098380e0a00801ca13040385c070100400440701c14090004c1c0700800a013070b81401000f02654040380e0a048001c07010280200158380e0a0080054040733414010004c1c2d050040040
|18=>0x50040013073c40e0a008002604060b814010004c1c070500400f0098380e06008a8260e1a01c14010d84c1c07278280200098201c070502400a6778300e0a00800260e0382812e10004c1c07770080200098380e0a008008a130701c1401003b4260e0390414010884dd80e038280200098380e060083c260e1881c1401002001ceb050042200098380e090b8e026ea
|19=>0x537c000e03818040108838620a0080090130701c0401088002e0e038182c02008001c0705004007e098380e0a0084554130701c1401003e0260e0382802007b84c1c3416828020009bd81c070500400130701c0c160502400430701c14010004c1c070504000130701c1401003d0260e0382800f3098380e0a04801e6130701c1409000a8880e038280211098380ef2
|20=>0x382802007c84c1c0705004225f098380e0a620002654060380e0a00800260c070c40e0a0080026040382802002904c1c070f01814010004c240e038080200098386207050040017098380e060500400e7098386831038280200099101c07030280200098301c2e038280200098481c07050042200098380e160502402000701d0801001e8260c0701c0c0a0484c1c07
|21=>0x4c1c07032100200098390e31038280200098380e060100400130701c1409003f0260e0382802111c04c1c0705004002a09910180e038280200098380e0a00801f6130701df40a0084400130701c14005f04c080e0382802110004c1c070102802002f84c1c070302802110004c1c8703828020009a3c1c07050040013040380e0a008014c130701c0c0a04800260e
|22=>0x98301c070500422000983814fd00800260e0382802005604d040e0380814010004c1c07050040036098380e0a0080100130701c140100168260c0701c14090004c1c2d188280200098380e0a00800d413070b40e0a00800a4130701c0c160500400130701c14e00004c1c070102802001c04c1c07050040075098380e0a048002e130701c1401001f4260e170b41401
|23=>0x2904c180e038280211098380e0a0080114130701c140100198a4130701c140100408260e1681c14090004c1c2e188280200098380e060540400130701d940a00800260e0390414010004c1c07010280211001501c070500400130701c140100400260e0382802006a04c1c070302802003d04dfe07050040013310380e0a008002656070b80e0a00800260e03829fc00
|24=>0x701c140900074260c0701c15010004c1c07050040086098481c070500400a3098380e1e0500400130701c140900064260e03ae014010004c1c0705004007709c101c07050042200098380e0a00801ce130382802008184c880e038280200098301c07010280200098380e0a0080138130701c1401002bc260e1a01c040a00800260e0382802005f84c1c31038280200
|25=>0x380802002904d320e038280200098380e0a0094400130701c140100414260e1701d08010004c1c070500422002904c1c070502400d9098201c0705024000e03808140100190260e03ad414010004c100e0381814010004c080e0381814010004dde080701c14010004c1c07050240066098380e0a0080154130701c140164000260e038042e38098380e0605004be13
|26=>0x53d40013040385a07050040013060380e060500426080701c040a00800080c038280200098380e0a420040066099ec1c070500400130741814010004c240e1681c14010004c1c070f02802110004c1c0705004005e098301c07050047013020200e0a00800260c0701c0c0a00800260e0382802001e04c1c070102802003a84c1c070b0280200098380e0a00800540e
|27=>0x98380e0a00800cc130701c14010004c1c07050240200098380e0a008003a130701c14010006427040701c14010004c1c2d038280200098380e0a00800c813060380e0a00800260e03b280c0a0080026e20701c14010004c1c0703028020009bbc1c070500400130701c0c0a0480400130701c0c010e84c1c07052dc02110004c1c070500401070701c14003884c1c07
|28=>0x1c070500400130701df40a0080026040701c14010004c1c07030280200098380e0a0080070130701c15010004c1c07052100200098380e0a0084400130701c14090004c1c31038280200
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ad61a761a1619b6195618f61896183617d61776171616b61665160615a6154614e61486142613c61366130612a6124611f51196113610d6107610160fb60f560ef60e960e360dd60d760d160cb60c560c050ba60b460ae60a950a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624e62486242623c62375231622b6225621f62196213620d6207620161fb61f561ef61e961e361dd61d761d161cb61c561bf61b961b36
|6,0=>0x422741b7414740d7406740063f973f273eb73e473dd73d673cf73c873c353bc73b573ae73a773a1639a7394638d7386738063797372736b7364735e6357735073497342733c6335732e7327732073197312730b730472fd72f672ef72e872e262db72d472cd72c672bf72b872b172aa72a3729c7295728e72877280727972727
|6,1=>0x5d675cf75c965c275bb75b475ad75a675a065997592758b7584757e65786571756a7563755c7555754e75477540753a6533752d6526751f75187511750c550574fe74f774f074e974e274db74d474cd74c674bf74b874b174aa74a3749c7496648f74887481747b6474746d7466745f74587451744b6445643e7437743074297
|6,2=>0x78d7786777f77787771776a7763775c7755774e7747774077397732772b7724771d7716770f7708770176fb66f476ee66e866e176da76d376cc76c576bf66b966b276ab76a4769d7696768f76887681767a7673766c7665765e7657765076497643663c7635762e76286621761a7614660d760675ff75f875f175ea75e465dd7
|6,3=>0x945793e7937793079297922791b7915690e7907790168fa78f378ec78e578de78d778d168ca78c378bc78b578ae78a868a1789a7893788d6886787f78787871786a7863785c7855784e7847784078397833682c7825781f68187811780a780377fc77f577ee77e777e077d977d277cb77c477bd77b677af77a877a1779b67947
|6,4=>0xa107a097a0279fd59f769f079e979e279db79d479cd79c679bf79b879b179aa79a4699d79976990798a6983797c7975796e79677961695a7953794c7
|7,0=>0xbe17bda7bd37bcc7bc57bbe7bb77bb07ba97ba27b9a8b946b8d7b858b7f6b778b716b6a7b628b5b7b547b4d7b467b3f7b387b308b288b226b1a8b137b0c7b057afe7af77aef8ae87ae17ada7ad37acb8ac47abc8ab66aae8aa68a9e8a977a907a888a817a7a7a737a6d6a658a5d8a567a4e8a477a3f8a378a2f8a278a1f8a178
|7,1=>0xdab7da47d9c8d966d8e8d886d826d7c6d748d6d7d667d5f7d578d507d4a6d428d3a8d337d2c7d257d1d8d167d0e8d077d016cfa7cf37cec7ce57cde7cd68ccf7cc96cc18cba7cb28caa8ca28c9b7c947c8d7c876c807c797c727c6b7c638c5c7c557c4e7c477c3f8c387c326c2b7c238c1c7c157c0d8c067bfe8bf77bf07be88
|7,2=>0xdb98db27
|8,0=>0xe357e2e7e277e207e1a6e137e0c7e066dff7df87df26deb7de47ddd7dd67dcf7dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 264 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x17044030ab050010500005001008a90e84d050000b8e105003050020901d070290504d0604d001490702a06008070010b077050000500109001070290b8e1050030500216829038010e84d050000084d05001050010382907001170200382905001050000504d0382903077050000084d05001170441704d170010382904018000290307705001050000504d0504d040180002906008070010f0770500005001
|1=>0xa010c84d0382a050000084d050010302605001009f51882a07199038021a0001704d0604d070010381a050010084d03877050003304d03802010020504d1a0001704d038290084d0002a0084d0002b0704d05001020070701d090b5070290097d07002039b7050440500005001040030200a0504d170030382905199038020504d0519100802070e10002b070f1188030005d0002a0504d030770500005001
|2=>0x500005001000e70402b0500005001050010604d0385d0002a010000504d0601d070010084d000290005d0002a0504d070290084d0704d0201a05001060290700100a2900008020070701d009f51882a17003038290004d0002a0702a1a00018829000650382a17039008a90e84d05000070010004d0005d0002a0084d2a028070451682a0004d0002905199038020b8e105003050020604d0602b070010084d
|3=>0x1882a03ade008450004d072d60080903a2b000083204d0504d0721d0004d170440004d03829050460004d0704d070010500107229000080504d0004d2a02b04001009f71882a0384d0384d0504d0519b03802052a9070011a00303809008af070460004d0700a0504d0304f050010704d070290504d0004d060c70384d0084d0707500028002730482b008ad070460004d070290004f0519903802050010e84d
|4=>0x719903802020070117f0504d0504d1704f053310704d0701a00029070296504f050016404d0031d03829000290704d03a29000080504d070010084d0704d6204d0097f070020084d0504d0000a0504d07001040000704d5f04d00877050002a02b0604d0381a050011882b0384d0004f07029038020384d17039038290b84d0002a010010504d040020704d048670382a0084d001490702a420010504f009f7
|5=>0x702917020038294382a00a2b000080504d0500103829070017384d05001038290504d07019000292a02b070010004d0504d0004d1704f038291704d0604f0504d2f84d0517d0700204018000291704d00029050440004d03024050017004d020040701d050460004d03801060b80504d05365048000004d0601d070011703203829050450004d05046073510504d1682a03801188030384d0304f0500100029
|6=>0x70290004d0304f050010084d050017004d020040701d050010504d0004d17003038290002a0504d0304f0002903026050010601f070011704d2b04f050017a84d0087505000048770084d0500004877050000e84d0084d0500006029070010602b0e84d0500105000040020204d0302405001051d50000b0504d1704f0307705001050003e84d1882a0384d03b1d050070084d0500305002071e90500109001
|7=>0x504d0002a0084d1882a0384d03801038290504f00029188010384d000290504d048030084d050020004d0e84d0500006029070016384d0082a050050004d00877050000701d0004d070020504d050010004d038450004d0601d07001040020704d0084d05001038460004d070020004d0097f070020604d070010384d07001038390702a05001070290504d050030384d05001188290384d000290382907001
|8=>0x7001000080504d0702a038020014b0702a038010084d0384d038290084f0500103005050010517d070020504d0004d0604d070015182a0004f0380a0504d0381a050010719100802070e1050021703903829008650382a0004d0700103b1f0082a070c60384d070090504d0701a000290c84d0382a0602b070010084d07001038010384d040030704d038010702a0304f05001020040701d0002b0504d0000b
|9=>0x4d0504f038290004d0702a048000084d0084d0704d000070504d008090504d0002905001038210704d0084d038020601f070010031d0082a050030500207002050010084d050000084f070010b84d0002a070290004f050450004d0382a0084d420010504f3304d03802070050004d0300705001070770002806029070010504d070010482b0084d050460004d038090504d040000704d0384d0702a0004d
|10=>0x50000382a07005038010080207001050010604f07001050010204d0701d050010500105000008450004d0e84e05000020070701d0087505000038010704d05001070010704d0504d0701d070010504f03802071990380203875050000702903801050450004d090020702905002070010704d038390500107001188030384d0000b0504d0304f050010e84d050000504d0702a0728d0004f001490702a00846
|11=>0x8290701d05001050020084f0504f0004d0084d0384d038020084d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2a300000000a08000000025308c8000000000007d000000001c3000000006881820588000000000004900000000111040400000000e20308000024c0810000000000000001c40000000000000005200c800000000000000000000000000000000000000000000300000000000000
|5,1=>0x10cc40300003f100003c30000000000038400003530c8c0000c440000bc800000000000000000000000000000000000000000000000002d2
|6,0=>0x26c49920000972258493324488e3230800000008b12248872210c831204880100007d300007a300007821d887421c887021b886b300006920000672190c622180800000005f1178400000005c216880001608562000054214c451213c800013484a31208462000000000000000000000
|6,1=>0x3a04e6238cce213844df23748db2360c0000000d620000d42344c00000000000000d010000ce20000cb33248c6331080000000c222fccbe12f080002e88b9100000002e0400000000000000b6200000000000b422c88b022b4caa32a08a62000000000000002908a220000a0227889c2
|6,2=>0x50c8000504800050040004f880004f453b24e8400000013914dc93524d053224c092e24b452a30001273490d23100000004885202474d1a3000118245891420001131000111200010e3430800000010a24208000414d0324048ff23f0cfa20000f823d88f423c4cef23b48ec13a4c000
|6,3=>0x650592263cc000000000063858b3620d86260cd8125fc80005f480005f057935d8d74200017225c096e200000005b456b25a48000000000000000005a0567159496325849601574c00056c958355880000000000554400000000000001541000153154494e353094a252454725148000
|6,4=>0x6f080006e89b736d0db226c09ae26b09aa200000006a45a8169c4000690c000684d9f2670d9a200019910000000658c0000001951
|7,0=>0x8e4a3728d4a3328c4a2f28b4a2b28a4a272894a232884a1f2874a1b2864a172854a132844a0f2834a0b2824a072814a0328049ff27f49fb27e49f727d49f327c49ef27b49eb27a49e727949e327849df27749db27649d727549d327449cf27349cb27285c827189c5170c9c217009be2
|7,1=>0xad86b42acc6b12abcaad2aacaa92a9caa52a8caa12a7ca9d2a6ca992a5ca952a4ca912a3ca8d2a2ca892a1ca852a0ca8129fca7d29eca7929dca7529cca7219c466f29b4a6b29a4a672994a632984a5f2974a5b2964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b2
|7,2=>0xae46b72
|8,0=>0xb286c91b206c71b186c51b106c31b086c110002c01afc6be1af46bc1aec6ba1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x203000101000080000020a00010000005140002400000c800006000001700000a000004c0000240000110000080000036000015800009000003e00001800000a800005000002000000f00000600000280000100000050000020000008000002000000
|1=>0x163a800b134004abe00207400102a0008120004080001c4d000c0000041400020400007770003630001b08000d8000068000030300015fc000aec0005750002b7800157c000aae0005550002a780014500008ea00044a000222800110000082400040d
|2=>0x42ab802117c0108aa008450004221002105001080a00840200420000204c001008800803c00401b00200d001003e00801b00400a002001001000000655d00224000111080088000042020021000010110008010004006002002000f1b40060c8002d5f
|3=>0x1c02200b13000508ba02845501422780a1134040818020057010008008001004000001984c00c426006155c03006801802400c00a00600000220980105140082328040090020028010008006220002956c0140b000a04800442600215fc010abe00855a
|4=>0x8422a842103420b88a10584c08262e840315c20020a10010108000704000102000020808040343af81a1d540c0f8a0607550303a28181d040c08ae06001502562c8123174088000042c5d021626810157c08080004020002002e01001100708ba03844f
|5=>0x2942279483514a30a9a50855d2842279417134a0988a50445728222a940113c84000041044720376d9019b7c80cc9e405ccc2026679001d5c8008ce40040020000008153004008642000000c0182848315c2402021200050843a6842157c2108be10845d
|6=>0x2ac0a8b100005704222b02194d430800a1040442226420a1134c0a99e60444f300233980111cc0082c588d452c062a95a3514a51aaa528d45
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xa03000200030000000f000312000500030000000000000000000000000000030003000003000003030000000b000031000003031700000008000002020000030700030200000000190000000003030000000000000000000000000300000000
|6,0=>0x4d1159451b031d031a000085000163000000006e0011005194120c0000032b1d8200036a00000500000000030000001044130a9c470300000000039600ac034e4b1d00031c50300a030000ab4e0327051d680079000d000303031d1d0320001100111f1d130000093900000347000303000305890300030a0347000000000000
|6,1=>0x48040a000000892a5703511d030007451b04229500110303a835055611000000000002050c0307024e00038f110000007500000000060018761e11841b1db500110011003a0043000211020000021d03099501320926009d7802000002013b08001111110005000c00461d00001115009e1d1d1d0403000377472f11490e6c00
|6,2=>0x100138e71030a4e040300000289030097000804500300471c002e000037
|7,0=>0x5dc9992aa75fb6a24a8b74b35a4c6124708666b065c6695d617f3d7cbeca559aba8cc21332aab7b1bc6160a19081166bbb7d2cd0c15f8714c425cc2a673f725c5fb8cf92be2a714261b421a63dcbbf3ca3c86d8a80889bc5385b4f8f6f29a07bce54a96fc3536264bda45e338352c7b2369fad2d8d414a7e6a735898cd3a2414
|7,1=>0xa53e
|8,0=>0xc0af9361917a34b9c6285dbe617bd1aea640
|9,0=>0x23
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_108 5 roots_108 ops++addP pm 2 dom_62 7 roots_62 ops++addP pm 3 dom_86 5 roots_86 ops++addP pm 4 dom_124 6 roots_124 ops++addP pm 5 dom_60 4 roots_60 ops++addP pm 6 dom_94 7 roots_94 ops++addP pm 7 dom_74 4 roots_74 ops++addP pm 8 dom_120 5 roots_120 ops++addP pm 9 dom_104 4 roots_104 ops++addP pm 10 dom_110 7 roots_110 ops++addP pm 11 dzo_90_4 5 roots_90 ops++addP pm 12 dom_30 4 roots_30 ops++addP pm 13 dom_92 4 roots_92 ops++addP pm 14 dzo_74_4 4 roots_74 ops++addP pm 15 dom_118 6 roots_118 ops++addP pm 16 dom_54 4 roots_54 ops++addP pm 17 dom_114 5 roots_114 ops++addP pm 18 dom_82 4 roots_82 ops++addP pm 19 dom_58 4 roots_58 ops++addP pm 20 dzo_122_4 6 roots_122 ops++addP pm 21 dom_46 4 roots_46 ops++addP pm 22 dzo_106_4 5 roots_106 ops++addP pm 23 dom_102 4 roots_102 ops++addP pm 24 dom_90 5 roots_90 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_90_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_74_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_122_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_106_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_90 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
|0,0=>0xaaaaaaaaa8a8a8a80000000000000000aaaaaaaaa8a8a8a9555554015555540000000000000000015555540155555402aaaaaaaaaaaaaaa80000000000000002a802a802a802a8055555555555544440000000000000000555555555555444400000000aa00aaaa000000000000000000000000aa00aaa0000155540001555400000000000000000001555400015152aaaaaaa8000000000000000000000002aaaaaaa80000000444444444444444400000000000000004444444444444444aaaa0000aaaa00000000000000000000aaaa0000aaaa0001555555555555555400000000000000000000000000000002aaaaaaaaaaa800000000000000000002aaaaaaaaaaa8000555555554444444400000000000000005555555544444444aaaaaaaaaaaaaaaa0000000000000000aaaa0000aaaa000154015401540154000000000000000001540154015401540282828282828282800000000000000002828282828282828555555555555555500000000000000004444444444444444
|0,1=>0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaa000000000154015401540154000000000000000001540154011001100002aaa80002aaa800000000000000000002aaa80002222050505050505050500000000000000000500050005000500000000000a0a0a0a0000000000000000000000000808080800000000000155540000000000000000000000000001540000000000000000000000000000000002aaa2aaa2aaa2aaa05050505050505050000000000000000050500000505000000aa00aa00aa00aa000000000000000000aa00a000aa00a1555511115555111000000000000000015555111155551112aaaaaaaaaaaaaaa80000000000000002828282828282828005500550055005500000000000000000055000000550000a0aaa0aaa0aaa0aa0000000000000000a0aaa0a0a0aaa0a1555555555555555400000000000000015555555511111112aa82aa82aa82aa800000000000000002aa82aa82aa82aa8545454545454545400000000000000005454545454545454
|0,2=>0xaaaaaaaaaaaaaaaa0000000000000000aaaaa0a0aaaaa0a001540154015401540000000000000000014001400140014028282828282828280000000000000000282828280000000555555555555555500000000000000005555550055555500aaaaaaaaaaaaaaaa0000000000000000aa88aa88aa88aa8955515551555155500000000000000001555155515551555088888888888888880000000000000000888888880000000555555555500550000000000000000005555555555005500aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaa0000141414141414141400000000000000001414141414140002aaaaaaa802a802a80000000000000002aaaaaaa802a8000555550505555505000000000000000005555505055555050aaaaaaa0aaaaaaa00000000000000000aaaaaaa0aaaaaaa155555555555555540000000000000001555155515551555002a802a802a802a8000000000000000002a802a80000000555500555555005500000000000000005555005555550000
|0,3=>0x2aaaaaaaaaaaaaaa80000000000000002aa82aa82aa82aa8000000005555555500000000000000000000000055005500
|_,_=>0
def sP:Nat→Nat
|0=>0x24704878624708121d18938704870624708121b1891c20486862476420481891d108860624708121718c2470810062431d10952091c24c12064891c24011893834412063c91c204018524e3412063090c20401c20482c62420482861440c2040
|1=>0x1c2048b86a1f1c20481891c2048b4626c1cd081206247acd0812067c9387081206247a820481842470900467c91c24012061470812291a87c734121f2470889869491c20481891c121e1898c308120624788204818980708120615f1cd081212
|2=>0x2470812062470812062473420481899070812062470900481a82473412062561c20401891f108120615f1c204819f2470950482470812301a82431c2048189bc7081206247442548189
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
|0=>0x464109542c11924649097c1c9193474219348421908749190904121248412124648057c8c919086491924267077c764091c647054464785247421924644192094d0708643071c65625206472104241191c641511c6441920947191c248192504805086421d14847251c647252064719
|1=>0x21904741210864909207481944641092464725046491924d82191c64909906411d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x6600000003
|6,0=>0x5449cd2900000088d08a013a66c8001920000000017200050c898f21a42c841862
|7,0=>0x2714c294520a31442845009f13c2744e09b1342644c09712c2
|8,0=>0x148688d01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x2014800d42a006257203029b008c6c0020fe40107ea0080a1003b5c80158e400a5720038d800197c8006360002000000a1000031000010800005720002b100010400008000002800000820000400000180000050000012000008000002400000e000000
|1=>0x6200c258040224087f91921dc8884ee43844200832f9
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x80001
|6,0=>0x2921c000525110300a00000300b3c318e148
|7,0=>0x5265dc7934235956dd8657e4658
|8,0=>0x32089a
|9,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 7 roots_188 ops++addP pm 1 dom_142 5 roots_142 ops++addP pm 2 dom_156 5 roots_156 ops++addP pm 3 dom_62 7 roots_62 ops++addP pm 4 dom_182 7 roots_182 ops++addP pm 5 dom_186 7 roots_186 ops++addP pm 6 dom_148 4 roots_148 ops++addP pm 7 dom_158 7 roots_158 ops++addP pm 8 dom_168 4 roots_168 ops++addP pm 9 dom_174 7 roots_174 ops++addP pm 10 dom_178 5 roots_178 ops++addP pm 11 dom_150 5 roots_150 ops++addP pm 12 dom_146 4 roots_146 ops++addP pm 13 dom_54 4 roots_54 ops++addP pm 14 dom_58 4 roots_58 ops++addP pm 15 dom_184 5 roots_184 ops++addP pm 16 dom_30 4 roots_30 ops++addP pm 17 dom_138 4 roots_138 ops++addP pm 18 dom_166 5 roots_166 ops++addP pm 19 dom_164 4 roots_164 ops++addP pm 20 dom_46 4 roots_46 ops++addP pm 21 dom_170 5 roots_170 ops++addP pm 22 dom_180 5 roots_180 ops++addP pm 23 dom_60 4 roots_60 ops++addP pm 24 dom_172 5 roots_172 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_172 _ g hchk
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
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030303000000000303030200000000030302000
def gsh_217_4:=0x3030303000000000303030300000000030303020000000003030200
theorem lowS_zo_217_4_73:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,72),(64,80),(64,192),(68,69),(68,76),(68,84),(68,196),(128,129),(128,132),(128,136),(128,144),(128,192)]
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
|5,0=>0xe89cc17b11
|6,0=>0xc6af1ab283a1544999461fa5c1bca31a438105f9
|7,0=>0xf1341eb3bbade05a3fc676be24768934f4b2d5e006f7c
|8,0=>0x820eb125d802ed9
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x444444440000000044444444000000004444444400000000000000033333333000000003030303000000000333333330000000030303030cccccccc00000000cccccccc00000000cccccccc00000000888888880000000000000003232323200000000000000000000000032323232c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c333333330000000022222222000000003333333300000000222222228888888800000000888888880000000088888888000000008888888b3003300000000003300330000000000330033000000000033003300cccccccc00000000c8c8c8c800000000cccccccc00000000c8c8c8cb3333333000000003333333300000000333333330000000000000000cccc000000000000cccc000000000000cccc000000000000cccc00032323232000000003232323200000000323232320000000032323232cccccccc00000000cccccccc000000008888888800000000888888880330033000000000033003300000000003300330000000000220022cccccccc000000000000000000000000cccccccc00000000000000033333333000000003333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8491058bd91058b396158c91058791058bd961058e391058b91f058e96058ba96058ba3658ed9605b926105bd921058e3965b921058c31058731058736543210
|1=>0x58b91058ba91058b39105
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863172a72371d61761160b6
|7,0=>0x7476d76766165985274b74563e7
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x245906e5316411064141ee5416e569441906c569c41106c51944191441906c5694418d9a53164110641b16363164141e41b96e991641ba64510641
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd434890234ca31cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x19ebcf063ae1d6efb77d27ad1d66fb37593f85de2ee0f585801d60c904000f8040000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x398617910a
|7,0=>0x14925736360e
|8,0=>0x1e29
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_93 7 roots_93 ops++addP pm 2 dom_216 5 roots_216 ops++addP pm 3 dom_205 8 roots_205 ops++addP pm 4 dom_153 5 roots_153 ops++addP pm 5 dom_213 8 roots_213 ops++addP pm 6 dom_220 7 roots_220 ops++addP pm 7 dom_157 7 roots_157 ops++addP pm 8 dom_156 5 roots_156 ops++addP pm 9 dzo_217_4 6 roots_217 ops++addP pm 10 dzo_89_4 5 roots_89 ops++addP pm 11 dom_29 4 roots_29 ops++addP pm 12 dom_92 4 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_217_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
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
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,10),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(32,33),(32,40),(32,96),(32,160),(34,35),(34,42),(34,98),(34,162),(64,65),(64,66),(64,72),(64,96),(64,192),(128,129),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>3
|5=>66
|6=>146
|7=>80
|8=>20
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x1e61b1115907eae
|5,0=>0xda5bbc37babdff7909128ce8c888b281ae17bc7c7930674fec712326e4456c822650cd5f9e55f1025a5f15912b548c0523d8500aa4f0b04e92f4e7074c5f447bc145858436d3409c23d1df3d13f3b4553a9bd387c33607b3601735dfb3208a2db3e2cc3c29b49294e825c60248dc23619210711eb751d250193c91909218b56174ad1409d117f1104320cc7d0c6520c03c0b21a06a57065dc0643d05e470579d0577201d1e
|6,0=>0x66fea63621633d06334b5be54590125878c56d2c568c550a02509b24fb5b4fa734f14a4dd924c6144a4d34a03249f2449a5347e1346bed4342142b3e403d23fd7b3f68f3f22b3e0e53e0e13d4a63cd203bf7f3b17138072369e336669356d333e123388f336ab3328932c2a310aa30ae83074a2fc382f90b2f8842ddc22d9c12ce162bb532988728b3228852282b027eb22558c224a12112f20ccd20acc1d23a1cb7f1be7b1bc611b72e1b4b51afb51abe01a07019e69197b8196f41950818421182371722b16ef41662916599158381475e143221312a12af212149119f0112e7101d90fe450f97e0f09b0ed220ecbc0d4160d1e80ce2a0cdea0b9140b5dd0ad990a8320989c078d6067330663c0656705e7b059b40579d0567c053e40486b047fa03646033530330f02cf40266f02582024fe01c9f01a5600c7000c2000af3
|6,1=>0xddf45c9256bdff7abc3aa5a039bf6294798944a7909128c45b83857818d07c7f877042727396e87d6dab7680ae
|7,0=>0xddf45d87e5ab777ab58b97027963d68e0f383180809207bd9a665b95fee854ee25263e4ce684c8974c4d44b36b482f742b25411503f4ad3f0613d4a93cb063bdc93a6df3a23e361e9353ab30f343086a2d306291aa2915a283032717326772266d22419023747218bd20b7b1f8da1eeec1c59e19ed9197ed180be1758616cbf16889160dd15c4e14e2d145241153a0e5df0e2ac0de7b0d3e70cb040c5ba0b9f80b3d20b3630afd30a9f30a8a80a7e309852080b3062b3055be049a204728046120443700ffe0065a
|8,0=>0xa2b7e688546689b5de5e5aa7e3fd043891e38690303302c79c2b93125c0f168de1439c12e870e79c0979904e7b04e4d025b7
|9,0=>0x7ccdc434562ff10040d9
|10,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0000000f0000000a0a00000a0a00000a0000000a00f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f00000f0f00000f0f00000f0000000f0f00000a0a00000f0f00000a00f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0a00000f0a00000f0a00000f0a00000f0a00000f0a0000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f00000f0a00000f0f00000f0a00000f0f00000f0a00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000a0a00000a0a00000f0f00000f0f00000a0a00000a0a
|0,1=>0x303000000000000030300000000000003030000000000000300f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0a10100000101000001010000010100000101000001010000010000000100f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000000f0f00000f0f000000000000000000000f0a00000f0a000000000000000000000000000000000000000000000000f0f00000f00f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0ae0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00f0000000f0000000f0000000f0000000f0000000f0000000a0000000a00000000000000000000000000000000f0f00000f0f00000f0f00000f00f0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0c00f0000000f0000000f0000000f0000000f0000000f0000000f00000000
|0,2=>0x50500000101000005050000010100000505000001010000050500000100f0f00000f0f00000a0a00000a0a00000f0000000f0000000a0000000a00f0f00000f0f00000f0f00000a0a00000f0f00000f0000000f0f00000a00b0b00000b0b00000b0b00000b0b00000b0b00000b0b00000b0a00000b0a3030000030300000303000003030000030300000303000003000000030000000000b0b0000000000000b0b0000000000000b0b0000000000000b0af0f0000030300000f0f0000030300000f0f0000030300000f0f0000030000000000f0f0000000000000f0f0000000000000f0f0000000000000f00f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0f00000f0f00000f0f0000000000000f0000000f0000000f0000000000f0f00000f0f000000000000000000000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f000000000000000000f0f00000f0f000000000000000000000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f00f0f00000f0f00000f0f00000f0f000000000000000000000f0a00000f0af0f00000f0f00000f0a00000f0a00000f0f00000f0f00000f0a00000f0a
|0,3=>0xf0f0000000000000f0f0000000000000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0a0000000000000000f0a00000f0a000000000000000000000f0a00000f0a0000000000000000000000000000000000f0000000f0000000f0000000000000000f0f0000000000000f000000000000000f0f0000000000000f00f0f00000f0f00000f0f00000a0a00000f0a00000f0a00000f0a00000a0a00000000000000000000000000000000505000005050000050000000500f0f00000f0f00000f0f00000f0f0000050500000505000005000000050000000000f0f0000000000000f0f0000000000000f0f0000000000000f0a00000000303000000000000030300000000000003030000000000000302f0f00000f0f00000f0f00000c0c00000f0c00000f0c00000f0c00000c0c3030000030300000303000003030000030300000303000003030000030000000000000000000000000000000000f0f00000f0f00000f0a00000f0af0f00000f0f00000e0e00000e0e00000f0c00000f0c00000e0c00000e0c5050000050500000505000005050000050500000505000005050000050050500000505000005050000050500000505000005050000050000000500
|0,4=>0xf0000000f00000000000000000000000f00000000f0f00000f0f0000000f0000000f00000f0f00000f0f0000000f0000000000000000f0f0000000000000f0f0000000000000f000000000000000f00f0f00000f0f0000000000000f0f00000f0f00000f0f0000000000000f003030000030300000000000003030000030300000303000000000000030050500000505000005050000050500000500000005000000050000000500f0f00000f0f000005050000050500000f0f00000f0f00000500000005003030000030300000101000001010000030300000303000001000000010000000000000000000000000000000000f0f00000f0f00000f0f00000000000000000000000000000000000000000000000000000000f0a00000f0af0f00000f0f000000000000000000000f0f00000f0f00000f0a00000f0a00000000000000005050000050500000000000000000000050000000500a0f00000a0f00000a0f00000a0f00000a0f00000a0f00000a0a00000a0a00f0000000f0000000f0000000f0000000f0000000f00000000000000000000000000000000000000000000000000000000f0f0000000000000f000000000000000000000000000000000000f0000000f0000000a0000000a
|0,5=>0xf0f0000000f00000f0f0000000f00000f0f0000000f00000f0f00000000005000000050000000500000005000000050000000500000000000000000000000000f000000000000000f000000000000000f000000000000000000f0000000f0000000a0000000a0000000f0000000f0000000a0000000a0000000000000000f0f00000f0f000000000000000000000a0a00000a0af0f00000f0000000f0f00000f0000000f0f00000f00000000000000000000000000000000000000000000000000f0a00000f0a00000f0a00000f0aa0a00000a0a00000a0a00000a0a00000f0f00000f0f00000f0a00000f0af0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000f0000000000000000000000000000000000f0f00000f0000000f0f00000f00f0f0000000000000f0f0000000000000f0f00000f0f00000f0f00000f000000000000000000f0f00000f0f000000000000000000000f0000000f0000000000000000000000000000000000f0f00000f0f00000f0000000f000000000000000000f0f00000f00000000000000000000000f0f00000f00f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f0000f0000000f0000000f000000000000000f0000000f0000000f00000000
|0,6=>0x50500000505000005050000050500000505000005050000000000000000f0000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x450aa522103090a8c88208184a322702060a2cca208502970818f870a44d0d0c4029222682060e2c1141c4c38b0800e890a58886201c28b4210a090e2d0022824e040c7c485167821d0e14d91340830716642141c24b1108183851634a13121458d0238512221880718080800608080
|1=>0x2189871611906124918b080432422118870a2c22f0e146840ca838516206805614581604c385522c22f0e1420656a83851680a130e14d840c7c3855a340860a908a71a184840ca84870a8c8840c242a908194070a2c694261c28b1a50a930a6d19108182a308043280a9c6a6021858d
|2=>0x2c438516103340e1459e1a50a85521031f0e153ba080438b7434085168822f0e145842839c07365c8820c24b9108c43852c1031f0e145990850005389d1040cac5a2080072b168820e3a1c59e1a08a090819bb60e15684023839222882060e2da8d0c1458462d0385226938d04185b3
|3=>0x21839622103070a882010cdc385462c2010c2428b44082141c1c58d040433f1634086261c28b3c34086122de8202383910819e070a6c9110818385389d10d080430b040433b122d10d080400e16882063a1c28b080400a0a2c1012a1898716802011c2458462ac3852c442310e14584
|4=>0x850005389c2010d085840200742229c206821c29b22341060e1459e1034a070a44d0d08182a71608206561c5840c7c385522c206121c29734043100e145842900385489c58d0218496229c2060e14d9144103070a9058d021849b389c1010c1c5a2080032b0a2df040cac38516cc402
|5=>0x4195870a2e28402184851610a130e14b8b0819a070a90e2708043093648582021838b1a08a000a2c2140110385342c206561c2a9161032b0e1538b441032b0e2cf04020070948702010c24584290c38516d42060e1489a4e082060e48e270804307226938d081828b40043130e145a2
|6=>0x404307161034c961c29216882010c1c5840d264070a4538d041838b10340951c14da744100860e2d98808047071718214121c2914e882060e6c9270804307161008e60243a416100b10e1458d045030916206812a2429738886810c1548b1a103070a5e38d021829222342060e14588
|7=>0xcd038506100860e1520b1a0808612588820818385365c8840c24296462c2010c145840d2c38516786820218491041033c0e1689108183851610330561c28b10642140e1490b1a080860e44206a02428b080432e122df010c4c38516342010d3829b48442060e1520402194070a6d38d
|8=>0x40782140e16b111a1838516786941c1c28b1a080801d55384021838516cc682021839716100b10e14e274410086168820100385840cd04870a2d102085000516f8104281c28b32100800c1538402194090e588a20818385229c2540c1c5820818f870a2e984280028b0898086126c584
|9=>0x16801140e14b0b0819a070a2c20162243852470584021848b3c340950c14b2422103070a2e284281c28bb010a070aa45840c1c28b081941f0e1489c44082060a9c584021ab872e10086501c2914e881040c1d191081838536441060e1458d0819a070a2c2011c19c072490584021838b
|10=>0xc1c28b40882010c1c2a42e702010c1c29c16882010c1538b1a080860e5858402183851688206681c28b08058870a582010ca038516882011cc039616100b10e1548b44103070a90d0b1a0430516103340e145be1010a070a2c20656743854e100860f682010cdc4870a2cf040cac385
|11=>0xc1c29616082010c1c29c4e342010c1458d080400e0a6cb8b08043090a2d00d04043070a2c1040219e070a2c68402194070a2c404036c38516cc68402183851620c840218385222e9840c1c2d116100860e14584021a8090a2c422021838536905840218385168820656243852e68201
|12=>0xe1489a081838516206810014d9c1610086121458402383390e145840cac3851688104020030516f81040218385229c1040c1c5a066100860e1458429703852c2d1040218385174c20100182a71612a010c1c58208043400e1458402198070a2c6840238309222d1020818385485c884
|13=>0x8043070a2c2010c1ef052c905840218385ac442060e1459e08507070a2c42204043070a5c58402183dd0a705a204100860b58e040218385369c2010c1c2a7168810402183a316100860e14d8b04043070a2d00d08047070a2d01e08043070a2c6810d2838516786811c183851620114
|14=>0xd5c38536446840c1c28b1a08a060e1459e085038516882140c1c28b7c202010c1c29722103090e145a208195870a2c404282438516882010cc038516801010c1c28b041032b0e145c608043070a2c2140c1e105362c6840218485222c6840c2428b0804307b41459e10100800e145d8
|15=>0xc24385365c584021838516202010c24385229c2060e1458402383090e2c2010d2838516782011c18385ac2c2010c1c2974e100860e14b8b04043070a2c2010c1e10516100860f8428b1a10a060e14b0b08043070a2c68202184a438082010c1c28bc0100860e16f8b08043070a2c201
|16=>0x2c2010c1c28b10100860e14584281838516082010c1c2a716100860e14588085038516881040218385362c6840218385482c2010c1c28b3c100860e1458d04043070a2d10402183852e2c201
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x8500440004
|5,0=>0x17c61766170616a61655160515a6154614e61486142613c61366130612a6124611e61195113610e5108610260fc60f750f160eb60e650e060da60d460ce60c860c260bc60b750b160ab60a5609f60996093608d60876082507d50776071606b6065605f60596053604d60476041603b60365030602a6024601e60186012600d5
|5,1=>0x18861826
|6,0=>0x331732a7324631d7316730f7309630272fb72f472ee62e772e072d972d362cc72c572be72b772b072aa62a4629e6297729072897282727c6276627062697262725b7255624e72486241723a7234622d7226721f72196212720b720471fd71f761f071e971e271dc61d571cf61c961c361bc71b571af61a871a1719b6194718e6
|6,1=>0x4de74d774d164cb64c564be74b774b074a974a2749c6496648f74887481747a7474646d7467646074597452744c6446643f74387431742a7423741c7416640f7409640363fc73f663ef73e873e173da73d463cd73c673c063b973b273ab73a5639f63987391738a7383737c7375736e73677361635a7353734c7345733f63387
|6,2=>0x5587551754b6544753d7536752f75287522651b7514750e6507750074fa64f374ec74e57
|7,0=>0x72e7727772077188711770a770286fb76f476ec86e666df76d786cf86c786c076b976b186aa76a3769b8693868c7684867e66786672666a8662865c6654864c8646663e8638663086297622761a8613760c760485fd75f585ee75e775df85d785cf85c785c075b885b085a975a2759b7594758c8584857d7575856d8566755f7
|7,1=>0x79f77996791878a7783777c7775776e7768676177598752774b7744773c87357
|8,0=>0x8306828882088197812780b780477fc87f487ec87e667df77d877d087c977c277bb77b477ad77a67
|9,0=>0x84a7844683d78367
|10,0=>0x8516
|_,_=>0
def wAt:=mkWire dB 98 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xcad44071a150c1d44071a15081d0e1116b900080c1d0a110e114e111615022d582f0cad440712112a13161538080e11161d0a110815081d00150c1d0219481f341302190e1508151a19081d381138150e2d022d30252e270e15082d2a130a1912200a1d0c110e110c1d1e2d1c340a110c150e1116290e1912200e150c110a11
|1=>0x1615022d1c1d02191c110a194407041d08150c9938081615161d08154c1938080e11161d0a1172151c360e110a1d2e1d082d022d16d22c07442d041d0815440712110a1d440712110e1512110a1d0219081d0a1d041908150c1516b900080c1d0815081d02993808161d08154e1d0e110a2d022d0e1502b900080c1d0815582f
|2=>0x22d7c2f4419041d08152c1f2e2516110a1d0c15041d0219081516260e150e110a117c131c350c150e110a1d081d04190815101f0c110c150815380b0a11161d022d36172e1d1611022d0a3516150e110a1d0a111a2f0e110a350c15081d02c2041d0815122008190c1d0a1d2a1312190e1500110c1d0c150e152c1b34114e1d
|3=>0xe1512130c1d0c150e151635081d022d0a11081d101508190219081d3815161d022d4407041d1615081516ae4407041d081516ad44071211341316250e15000b08150e190219081d4e110a2d481d4e110a2d16351a15022d081d4e110a1d1615081d0a113811161d440712110e154407041d08154017101d081934114e1d1615
|4=>0xc110a1d2a131c1d0c1502192c07481d2e150a1d161d4e11161536171a2d081d0e110a110e1902194407041d08154407041d0a111c110c150c1d0a1d0e151609161d081502190d0912130e1502993808161d08154e1d08151615022d36173811161d081d4e1d0a2d022d2a13001500110e1902190e1912110e15161d12131615
|5=>0x42f08152c17442d041d0815941d0c0a081516150815022d0e11081d1c1d0a191a2d0a351615081d4017101d08191027081902190a35081d1615022d36171a2d081d441b08250e1508150e150219081d12190a1d0c1116111a15161d081d16ad44071a1516110a72161d081d022d36171a2d081d08194407041d08158c1d1027
|6=>0x41d022d08152e1d0a1d082d022d461d481f042d081503329a1d160a0815081d0a1d041908151605380b161d1605a4152e1f082d441b041d08153c1f10150819021936171a2d0e1138130a1d161d022d040008150c1d0a1d2a112a1312190a1d9e1d4e371615081d2e1d2e15082d022d1609442f041d0815163516150e110f35
|7=>0x17054e3616150e1140171a190e110c5a481d2e151615161d12110a1d0c150e1912110e152c072e2516110c1d041d02190815000908150e1902197c1f2a1100150e19168a12110e15442d041d08151615041f022d0a11228a041d022d08150c1d1a170219081d38080e15161d0815162910240c110e1516090815081d0a1d1689
|8=>0x1017081902190d4d1a170219081d4407041d0815442f041d08150e090a11161d022d0b054e3616150e112c2f481d2e15082d1615041d022d0a111605481f042d081508152e1d082d022d2c074e35161572151c360c150e1136172e152e1d1611101d0219101508192e17081d082d022d0219081d1c110a190c1d0a110c150e11
|9=>0x8152c1b442d041d0815442d442f041d0815441b041d0a112c1b442d041d081516ad4407041d08150e114e114e1d16152c07442d041d08153c1d101508194407041d08152e24161516110e1516fa10250c1100110a110e1902192c07442d041d08152c1b2e251611361738110e2d1c1d081d1c110a19481d4e111615022db21d
|10=>0x1615081d0a190c1d081d2e1d16110a1d08151a19081d380b161d442f1a15081d1c1f0c15081940171a19081d3c1f101508191a17022d081da4152e1f082d0872161d0a1d0819041d08152e152e1d1611440712110e15162516110e151a151a19081d161d2e151611161d1a15081d0a1116150e1104f1380b161d0815442d041d
|11=>0x41b0a11081d1c110a190815081902194e1d1615022d0c1d0c110e110a1d38110e2d1c360e114407041d08150e090c1d081500090c1d081508151615022d40171a19081d00130e190219442d041d08150a360c1d081d041f16150815000b0c1d441b041d0815081d0c150e15041d022d08152e15082d022d3809161d0815161d
|12=>0x81510270c110e15021912130e150e151a2d081d0e15022d081d2e2416110e150c1d101508190d4d1a170e1110260c110e15481d042d08152e171611022d02191c110a190e090c110a112e260e150e09161d0815161d2e17082d16151a2d081d041d16150815481f042d081508151a2d081d0c350c150e11101d101508190e11
|13=>0x1c110a192e17082d1615082d16110a1112130e15121b0e150219081d442d041d08150e150e110a111609161d081508fd122f0e15170912130e1576151636081d1a2d022d081d08150219081d1015081902190219041d08153c1d101508190a1d1611022d4407041d08150e1508190219441b041d08150a111a190e114407041d
|14=>0x81902190815161508190219041d08151a2d081d4e111615041908150e110a11041d081516110e152e1d16110c110e151615022d0c150e150c0a0815
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x198006
|5,0=>0x1e907731c946d500006a319900001854000178c5b3164854500004f500004a500004640000415000000000003d40e50000000000000000000d143040b1000000000000ac4000000026508540000804000000000007c40000000000000000006940000000164000012404440c5
|5,1=>0x7e5
|6,0=>0x570c000561155354514e3529146450913e44e913734cd13034b100000001293498d22447911a4459112443cd0b441d10343fd0fb40000f743cd0ef43ad0e74390ce133750da335ccd3433d0cc3324cc6330ccbf42ed0b742cd0af42ad0a7428d09f426d09832510913238c8a421cc834
|6,1=>0x91524148f523948d8e3338bd22b489d223487d21b4860e14484120c482120448011fc47e4df637c91ee47acde7478d1df4770dd937551d147351c940001c547051bd46e51b546c51ad46a8da6468cd9f4670d9846511904631188461118135f8d7a45dcd7345c0d6c45a4d66358915f3
|6,2=>0xa0927f39ed27749d0e7049b126849912613978e5a495cc00094d24f4930e493
|7,0=>0xcfcf3c3ce4f363cccf303cb4f2a3c9cf243c84f1e3c6cf192c58f133c40f0d3c28f073c10f013bf8efb3be0ef53bc8eef3bb4aea3b9cee43b84ede3b6ced83b54ed23b40acd3b28ec73b10ec13af8ebb3ae0eb53accab03ab4eaa3a9cea43a84e9e3a6ce983a54e923a3ce8c3a24e863
|7,1=>0xdbcf6c3da4f663d8cf603d74f5a3d5cf543d44f4e3d2cf483d14f423
|8,0=>0xe60b962e50b922e40b8e2e30b8a2e20b862e10b822e00b7e2df0b7a2de0b762dd0b722
|9,0=>0xe7479c1e6c79a1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0xc2000300000a20002800009800020800070000188000600001280004800011000042000101000400000810002000006100018000049000104000400000840002000006000010000024000080000140000300000400000
|1=>0x14fa004bc9012e200420001050404000008fe4023e9008de402200006fa401b68004fa4013680042000104000400000be9002800009c1001a0400621001424003f9000fa4003e8000f240038d000e0400368000d8000320
|2=>0x94d0024be9092f2424b88092e0024b41092a20243c9088800213e9080fa420200048da412320048c201220004058410141040460101100400000d14003040009be9022f2408a880224200880802042005b48016900053e9
|3=>0x200fa480080200080800181a0f24613c01844206008018008050379140da4483e9120400443c9110400423e9108d2442269104fa440be9102d24403e9100304323e90c8da4323200c8c20322690c8820303790b0f2425348
|4=>0x380c84e0289380704e0188380584e01293804a0e0109380204c1008300c84c00802b0104a13e9280fa4a03792805e490369222fa488b082227248898822232488388210f24823f9208fa482318208564821382081e481be9
|5=>0x3803f9cc8fa5e01287005a1c000864052180358580fa560108480fa512348440fe5103e8440d6110348408fe5023e9408f25023c8408d21003f9400f2100120400184e13e9380fa4e03c9380ea4e0369
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x203
|5,0=>0x100000130a292a002f36000b00080f2f450029001b00140019000000111700000000002b07040000003a00004f4a00060000004b00000000004100001e000b3a2c
|6,0=>0x180c34330d01b40912b8a7b21110011aa94493092d119b9d04793b107da5b7155f750024824e5001218a11aa014336ae7201121a0157010101b649203c04b9507e0033719f1164521c05321182576000000d088a8333224d364c017a6f6b006346af1526044c3f7c0ba681500f3054250105966e12898bb051778f78313e735a
|6,1=>0xb01090b941009160e0b0f370400420b0454
|7,0=>0x27a3826a6a55bb9248a469aca135975da12e6d66b5388c556a0cab489e119953679a27675b1d878a80b15e660f279c3bbc5c400e588e11277bbaad4e626165591195473d88b3388ea21f98762384a090
|8,0=>0x35a168868d91a370686ca8747f8d3839856a6a56
|9,0=>0x2e337f28
|10,0=>0x27
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 9 roots_233 ops++addP pm 1 dom_74 4 roots_74 ops++addP pm 2 dom_194 4 roots_194 ops++addP pm 3 dom_171 8 roots_171 ops++addP pm 4 dom_75 5 roots_75 ops++addP pm 5 dom_203 8 roots_203 ops++addP pm 6 dom_202 7 roots_202 ops++addP pm 7 dom_234 8 roots_234 ops++addP pm 8 dom_227 8 roots_227 ops++addP pm 9 dom_107 8 roots_107 ops++addP pm 10 dom_138 4 roots_138 ops++addP pm 11 dom_226 5 roots_226 ops++addP pm 12 dom_232 7 roots_232 ops++addP pm 13 dom_195 5 roots_195 ops++addP pm 14 dom_170 5 roots_170 ops++addP pm 15 dom_106 5 roots_106 ops++addP pm 16 dom_139 5 roots_139 ops++addP pm 17 dom_163 5 roots_163 ops++addP pm 18 dom_43 5 roots_43 ops++addP pm 19 dom_99 5 roots_99 ops++addP pm 20 dom_201 7 roots_201 ops++addP pm 21 dom_225 7 roots_225 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_225 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 9 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffffffffffff0000000000000000,64),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 66 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 66 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 146 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 18 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 146 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 80 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 20 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 20 0 = true)
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
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,18),(16,80),(16,144),(32,33),(32,96),(32,160),(34,35),(34,50),(34,98),(34,162),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(64,96),(64,192),(128,129),(128,130),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xfc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_242 8 roots_242 ops++addP pm 1 dom_179 7 roots_179 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_241 8 roots_241 ops++addP pm 4 dom_227 8 roots_227 ops++addP pm 5 dom_211 8 roots_211 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_211 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 8 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_183:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_159
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_222:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_221
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_175
def isoMvS_238:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_123
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 11:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_235
def isoMvS_250:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_123
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_126
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_190
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_222
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_235
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_249
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3030303030303030303030303030303030303030303030303030303030303030,16,20)] (by decide +kernel) lowS_249
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(2,130),(4,20),(4,36),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,18),(16,20),(16,80),(16,144),(24,26),(24,28),(24,56),(24,88),(24,152),(32,36),(32,40),(32,96),(32,160),(34,38),(34,42),(34,50),(34,98),(34,162),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,96),(64,192),(68,70),(68,76),(68,84),(68,100),(68,196),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x15555555400000001555555540000000155555554000000015555555400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005500550055005500550055005500550055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111111111111111111111111111111111112aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_190 10 roots_190 ops++addP pm 2 dom_250 10 roots_250 ops++addP pm 3 dom_246 10 roots_246 ops++addP pm 4 dom_238 10 roots_238 ops++addP pm 5 dom_222 10 roots_222 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_222 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
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
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(32,96),(32,160),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,96),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>4
|8=>45
|9=>158
|10=>134
|11=>40
|12=>7
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xdfcddcc178ca49a81a5a
|8,0=>0xf7a99f3ceaee1c1ea5e6e8040e3f34e18b1da3b6cfe1fcbf2cc8b05bc014b9336b3e84b343fb1faca657da1f4da1818a00799f195933bd92a18823d780a877425e5e4af5b0b359c465627d4c0a94ab194879943e134251441d2b32464239a6195f41772215a440cc6c07b790750c05636
|9,0=>0xcd343cbed6cb2acca856c9d68c9b1fc8e2dc8bcfc23e0be339be046bc0debaa29ba876ba297b9ed1b6fefb664ab4c35b3f4eb3509b2076b173db0943ad412aa7d4a438ea2a3ea01439f6349ec8f9e9c4995299908898843927cc91881914778e50e8cc878b55b8abb988ed888cf78527d8518e847e9820e78102580b51802187fe7d7fbd67d4f77979c78262777ce766c27626b745bf71ae96eca66d6946d109696ec680b8628b75e5795c8765bbd95b3e35a2d05646f55ae05381751ec751d314feaa4cee34af404abe349e7e4978c4886344114425de40fda3e8ad3ad953a94237a2134a5e348a5331793144630af62f4de2e5cd2d0542cec02ce5b2cdac2c40729ebe25702254492423c23a7022c381f2c81ef901e12f1a7c219746196be14b440cd360970108b71085cb075d606c9d0620204ad602453021ca019fd00f0f
|9,1=>0xff207fd8b7fd6fefc9c4fc01ff994ff4d66f4667f3ac1f2d17f0895f0300ecfe0ecbf1e8bf8e810adff1cdf63fdf4a9de967ddfc2d91d5d84b9d67dbd4dedd2b80d10f2cfee9cf9eacf05b
|10,0=>0xf6a56f5d7ef2e92f2de1f204cf17ddf03caf0275ee388edbf2e0f36e0be9dffe6dc7f7d77fcd69c4d1c8dd0310cffa1cf125ce406ccaa2cc8decb895cb376ca920c9fe9c9e32c86ffc5aa7c4157c3f9ec07bbbea0ebe110baaf3ba361b6a4bb6321b4038b1807ad94aaca28a9af8a5650a2b08a0e2a9f6fe9f1509ed599d9329c5a59af3d9890d97992958fb957379347c9077b903bf8ebe58e17a8b9d6898a584ec5848e684520802e27b991798667826276fad7692576335731fe7319f6c40d6ac2e69c83692de679036585564c9f642fa5bed05bca35a39a5987355baa5352751dfb4f7dd4ee384c81a4be754b00a4a74949f4848a6b478c54592a44e1044c7c441c341c7a4174b3fdf93e06e3ae5f3aa0c3554626ec5267e8249262430622d021fe801f3921c380195e11661e14cce13ddb1071e0e7030d4730cee406d67
|10,1=>0xfd981fd7c8fb2fefb145f9a19f73fb
|11,0=>0xf9668f2f5ce469ad9c9dd6a8ec6a49c3e3fbc505b6b15b4102b08a3a571aa30979d9fc96f2d9608e95801871327921a77077732c86c4d76bef066f0c642dc64123616d65fd8651a4a4ea873d84d35a802bfee24a6b1884614d98130ba0ee2d09e0809463
|12,0=>0xfff0bdd9d2c42d299b3f792e40eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff0000000000ffffffffffffffffffffffffaaaaaaaaffaaffaaffaaffaaffaaffaaaaaaaaaaffffffffffffffffff00ff00ff00ff00ffffffff00000000ff00ff0000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffaaffaaffaaffaaffffffffaaaaaaaaffaaffaaaaaaaaaaffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
|0,1=>0xffffffffffffffffffffffffccccccccffccffccffccffccffccffccccccccccffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffff00ffffff00ffffffffffff0000ffffff00ffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ffffffff000000000000000000000000ff00ff00ffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00fffffffffffffffffffffffff0f0f0f0fff0fff0fff0fff0fff0fff0f0f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000fffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0ffffffffffffffffffccffccffccffccffffffffccccccccffccffccccccccccffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|0,2=>0xffffffffffffffffffffffffffffffff00000000ffffffff00000000ff00ff000000000000000000000000000000000000000000ffffffff00000000ff00ff00ffffffff00000000ffffffff00000000ffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffff00ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff000000000000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff0000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff0000000000000000000000000000000000ffffffffffffffffffffffff00000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff000000000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffffffffffffffffffffffff0000ffffff00ffffff00ffffff00ffff0000
|0,3=>0xffffffffffffffffffffffffff00ff000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ffffffffffffffffff00ff00ff00ff00fffffffffffffffffff0fff0fff0fff0fffffffff0f0f0f0fff0fff0f0f0f0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x5c875424409300c5941442820403115044c031b20970704031058404031b5c62191441d300c2142c41d300c5c84443c100c40b10a3c100c5941440874c030b1151c03064541024c03091121c13104440c10104443810102c438a0401440c2040
|1=>0x1024c031110304018874404031b5c620911f1c13105041d300c5c82447ca04c20b10e1c100644438100621d50b10a08100c4542c409300c5852c478a0403111444c031b20510234100c24448204c19d14b11e08100c2440c20401941441d300c
|2=>0x10a08100c2440c70404051031c100860404031b5c621814b10a08100c5091024c031b24438704040910e28100810100c6d71886051074c03172098070403107452c409300c1441d300c5c844434100c4185041d300c5c86052c40874c0311505
|3=>0x24408100c4142c41c100c5c62052441c100c88859414408704030624408100c85061d24404031b18825c1c100c1884541020403066142441d300c2162c910a0403105852c41c100c41614b10a04030874b11e1c100c19814910a08100c214149
|4=>0x4031b18846310204030624428f04030814b11e0870403111447820403084542c428100c20910234100c1981070403171884541441d300c2191441c100c1886052441d300c2142440874c03091151c030621d2c408100c18911e04031b188745
|5=>0x19110a04031718845410100c6c621824404031b18858b24478a0403067452c41d300c2119841d300c2112c478100c1912c428100c4162442820403105851021c100c40910a1c100c90858510a08100c2091073c100c41824478100c6c62112c4
|6=>0x1074c032421150510a0403085091074c031b2142442820403162441d300c41d2c428204030644b1024c03065851074c030824478a04031b18844b1280403065942441d300c2141441c100c5c62091074c032740511e1c100c5c875424408100c
|7=>0x30860910704030620b10704032a41824428100c6c62052441d300c6c87452c41c100c41198428100c21d24408100c41d14911e08100c2112c478a0403065841c100c5c620911f1c130620910a04031b18844510100c6c621814b10a1c100c209
|8=>0x5851070403102c41c100c5c621614428100c22d2c41c100c18858910100c6c62052c478704031114478100c21650910a04030824428100c9d04542c408100c19850b2441d300c22c24408100c18844434100c1886161070403171884541074c0
|9=>0x38704018874910a08100c41124409300c41410704031718814b1021d300c4451024c030860b107040317188244c0700c18861624404031b18850b2440874c030980704030620510a1c100c5c850910a04031b20b2441c100cbc658910a040310
|10=>0x1c100c5c621d5091074c030814b11e2870403051074c032921114478a0403082c408704031719110204031718860b2442820403066141070403171886052c408704030645414408100c1985052441d300c21150428100c20524428100c6c8244
|11=>0xc4181441c100c5c62142c910a08100c58b2441d300c40510734100c2091121c130621614b1074c03086052440874c03085052440874c031d2c41c100c411144c4100c21d14b10204030624478204031b1882440c70401882441d300ca50144
|12=>0x7441c100c5c62091021c100cc8660910204031b18850910204031b19d1491024c030844b11e08100c1961447870403082c41cf0403064443c100c1887441c100c5c621114408100c4052c428204030910204031b1882c910204031b189107341
|13=>0x2442870403251886142441c100c18874b10a1c100c4112c41d300c4162440874c03102c478704031719111e0403171885851021d300c21d24404031b1887542c42870403081441c100ca504542c41d300c23324428100c1881491074c031a218
|14=>0x5c622d2441c100c1884541441c100c1886052441c100c1886091021c100c1885091021c100c1962441d300c18874911e1c100c18874910a1c100c4084491074c031020911e1c100c5c62091074c03271882441c100cac62182447821c100c188
|15=>0x28100c9c620910704031a1882c910704031b1882631021c100c1852447821c100c2142c910a1c100c2342441c100c18861d2441c100c1882c41c100ca8621d14b1070403062119841c100c1887491020403062182c910a1c100c1882441c100c
|16=>0x1c100c9062142441c100c6c62332441c100c18858910704031019624428100c18858510704030620b24478704030644911e04030620b24428704031044910a0403102165091070403062111441c100c4082441c100c9d01852c4287040308244
|17=>0x4c0310b091070403062052441c100c6c62052c41d300c21414910a1c100c2142c91074c030874910a08100c1882c91021d300c19124409300c1882c910704032e18860911e1c100c1882c9107a0100c191244a0100c188244287040317188244
|18=>0x1882441c100cbc621d2c41c100c1882441c100ca902192441c100c1887452441c100c40898910a1c100c20b24478a1c100c1891074c032918844911e28100c1886142c91070403062091070403214084541070403062182441c100c1882c9107
|19=>0x1882440874c031044910204031018b24428204030614b1021c100c1918c41c100c1884451020403062141491074c030814911e1c100c21824478a1c100c18850b2440870403062441cd0403062162c91074c03062111441d300c211244c4100c
|20=>0x2c41d300c1885891021d300c1882441c100cc862352441c100c1882441c100ca5019d5091070403062051070403291881491021d300c2091021c100cac62262441d300c2185052441c100c18860910a1c100c18814b10704031058911e1c100c
|21=>0x3086162441c100c18824408100c8462162c91070403101891021c100c5c62162c910a04030621114428100c20910704031b1885852c41c100c18860524408704030620910704032218850524408704030650910a1c100c21d2c4287040306211
|22=>0x21150b1070403062112c408100c1982c91070403062052441c100c6862052440870403102441c100cb86205244282040308749107040310205244c4704030874524408100c1882442820403102441c100c94621d1491074c030814911e287040
|23=>0x1070403101882c910a1c100c1881491074c03082c91021c100c19124408100c18844b1070403101962440870403101912c428100c18858910a08100c1885851021c100c1882c911e08704030644911e08100c1882441cf0403062142441d300c
|24=>0x1c100c1882440874c0306209107a0100c18844b10704030621624408704030621d2442870403062112441d300c18824478704030620910a1c100c4082c91074c03062162c910704030621d2441c100c1882441c100ca462098c41c100c188449
|25=>0x403062052440870403062262441c100c1882441c100c9c62091021c100c40624428204030621414910704030621124428100c188244c470403062111441c100c18824478a1c100c1882441d300c4082c91070403101852c41c100c18850b244
|26=>0x1c100c1882c91070403062091074c030620910a1c100c1882441c100c4062052441c100c18824408704030620911e0870403062142441c100c18814910a1c100c20910704032a1887452441c100c1882441c100c8462052441c100c408589107
|27=>0x9107040306211244
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x12600c600660006
|8,0=>0x173716c7163915a9152814b7144713c8133912c7124811c8115710c910390fb80f470eb90e470dc80d570ce70c770be90b680ad90a5809e7097708e9087707e9076806d9065805e7055904d8044903d7036702d9026701f70187
|9,0=>0x3a5939d8394938b9381a37983709367935f8357834e9346833e8334a32c83239319a311830892ff92f692ed92e492daa2d192c982c182b982b092a7929e9295928d8283a27a9272826a82619258924f9247823e9235922c9223921b8213820b820291f991efa1e691dca1d481caa1c281ba81b191a8919f9196918d9183a17a9
|9,1=>0x5d985d185c895bea5b595ad85a5859c9592a58a8582857995709567955f8556954d9544953aa530a526a51d9513a50b850294fa84f194e984e094d884d084c6a4be84b4a4ab94a3849a9491948894808478846f9467845e9455944d8445843c9434842b9421a41894108406a3fe83f593ed83e3a3da93d193c983c183b7a3ae9
|9,2=>0x6e396db86d296c996c096b796ae96a4a69c8693968a96819677a66e9664a65b965296499640963886308627961f8617860e960595fd85f3a5ea95e19
|10,0=>0x93da934992aa91fb916990d990498fc88f398e9a8e188d7a8ce98c4a8bb98b298a8a89ea895988c9882a879986fa866985d9854984b9842983998309827981da814980b980297f997f097e6a7dd97d3a7c9a7c097b6a7ad97a3a79a97919786b77d9774976aa760a756a74d9744973aa730a727971da714970b9700b6f6a6eca
|10,1=>0xb90ab879b7f8b75ab6d8b63ab59ab509b479b3e9b359b2c9b22ab1a8b119b089afeaaf4aaeb9ae1aad7aacdaac58abc9ab2aaa7ba9e9a94aa8b9a81aa789a6eaa659a5c9a539a49aa409a379a2daa258a1aba10aa0889fea9f689ed99e499db99d299c999c099b799acb9a2a999998fa987897e9975996c9963995a9950a9479
|10,2=>0xbcb9bc1abb89baeaba4ab9aa
|11,0=>0xd3bad329d299d209d16ad0d9d049cfb9cf1ace89cdf9cd69ccd9cc3acba9cb19ca89c9eac968c8d9c849c7aac719c689c5f9c55ac4bac429c399c309c279c1dac149c0b9c029bf8abeeabe68bdd9bd49
|12,0=>0xd7a9d719d698d609d579d4e9d459
|13,0=>0xd838
|_,_=>0
def wAt:=mkWire dB 54 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x25a411914287212464119609d41d2c649211884508246491d1c8471924845081c84919148411924649091c84f0524845081c849192c64921046491d1c846213404b281c6492134c4b281c6462124749213cc4621142091924747212484f3114209191c8471934c4b2824849191c84719
|1=>0x24849291c64b19248411924747212884b1d1c64921507c91d04645212464b2824849191c847191c84d012ca0719248451d24642191c8472134c4b281c64921046582750745212464521046451d1c84919148491924247212474119507c941188462110d4b281c64921607d8272c74921
|2=>0x1c849191c8451d04649192484119609c5091c849192ca0719188491d2484119609d41d2504621142472124747210464521246491d34c4b281c64921609d81f24a47193c0462114207212464119609d41d25046211c64f0114207212464f3124845081c849193cc4508246491d1c84b19
|3=>0x1c649212c7492124646212c749191c64921288492124a471914249191c8471914849191c847191884d312ca0719248491934c4b281c649212ca49191c649211c84119507c9411884f3118845081c849193cc450824647211c6541f609d41d250462104658271424721246443d1884508
|4=>0x148491925a450a1c8491904645091c8491904649411c846213c145081c8491924849291c84719607c9791d046211c8451d2464621609d41d2c64921686450a1c8491914849192424721188472124a8719607dd2124a471910d4b281c649211c8491d2504621507411925046212c74621
|5=>0x1c849211c6462124749211c649091c8462124649091c846219464b2b1c6492124249191c8471918845081c84919607c9791d04621247541f2c649212474b1b1c8492114209191c8471924649210864721246491d08647212c6471924749211c84b281c64921257497a1d046212474119
|6=>0x24a4719248411924747212c741192464921607c9792884719247421b1c849210464b1d2c64921609d41d148491924281191c84621246497a1d04621148451d1c84919247497a2884719507c91d2504621507541f25046212c74a211c6492114741192464921046491d148c9192474219
|7=>0x1484919147492124646211c6491d148c91918849291c84719086451d1c849192884719247492125e890908647213c045081c84919607dd2124a4719247541f14849192ca49191c64921a4641192c7c92124745212464719046541f25046211c649411c84621448411924746211c84921
|8=>0x1c8471926e4b2a1c64921507cb1d2c6492124642191c84921247474124646211c64b1d2c649211c6490a1c846212c6491d1c84921046541d2c649211eb450b1c849192474b281c64921609d6192c74921046491d25046210ab450b1c84919147c9212464621607dd2124a4719046541f
|9=>0x1c847191c841192474621609d41d25046211c84119246492124641192474721609cb291c649213414b281c64921607d6192c749212c641191c8492110f45081c84919246497a2884719507c7192504621b884b2a1c649211c649091c8462124649091c84621609cb291c649212464909
|10=>0x1884b1f24858271424721246451d0464521246491928847192484b1f04649192484a2124749191c6497a24842191c8497a24742191c84b2924847211c65827507494118845091c8491914849192474721507411914849191c6491d2504621507c52124647193cc45081c849191884929
|11=>0x25e42191c84721507cb1924846212ca07192485827142472124647212c647192484b1d248411918849192ca07192484d012ca07192484b1d04649192484119142472124647210464521246451d248491918849192474a231c647211474919248581f25e42191c84d312ca07192484119
|12=>0x2484919188491d0464b1924847952cac71924841191428721246582774849291c66b21142c721246581f25e42191c8541f250472118841191474721246491d24842191c8491924242191c8492114207212464508246491d1c8582774849291c64621246491d1c8492124647211c6581f
|13=>0x18841192c7492128849291c6462124a4719046491d188497a1d04621046490a1c8450b1c8491925e42191c84b2b1c649215074941188462124849291c64921046491d18849090464721188497a0864721248491d25e8741188411924649091c8581f74849291c64b1924849291c64b1f
|14=>0x2464621242872118849191c6492124287211c6450a1c84919507cb192484b1b1c8492124642191c84b191c64921586cb1d2485d2124a4719147c919248451d2464921247452324649291c847192ca4719248497a1d046212714a231c6491d14849191424721246497908647212504721
|15=>0x14849191c641192c6492124a47211c641191c84921046491d1c84b2a1c6492125e4741188421b1c84921086c91d1c8497a2884719a464b1f248541f25046218c74b1b24849091c8462124247211c64b1d24649210864721248421924747211884719248471924746212c74b19248491d
|16=>0x2484b281c649212c74119248491924741192474a231c6612124a8719446491d248451f2464621268421b1c8451d24646211c645232464a211c649210464b1f248491d28847195074b19248462124a87192474941188541d25046212484119188661d148c919507c52124641192464921
|17=>0x147c919748c9291c646212c7c921148451d24649192c7c9210464721246450b1c849190464523246541d148491974849291c64921246462124242191c841191c84621247472118849211c8471924647212484b1b2474921246491d1c8411914849191d04919188497928847192c64721
|18=>0x2464a231c6451d1c8491918847211c64b2b1c64921046451d2464a2124647195864b1d248472124a87192c74921188497a08647212c74719248491d2464719507c9411884b1d246492114247212466719242872114847212464719250462124849291c64119247492104649091c86a21
|19=>0x2484b1b248491d188471924849190464721248491d1c84621247492124247211884719247492124247211c64919242472124842191c8491d08647211420721246411925046212c6491d248491d1c849212ca4719248450a1c8491924647211884b2a1c6492124647211c6451d2464621
|20=>0x18849191c6451f246451d246492a1c649191884b1d24847212464523246490a1c8472118847211c64521246491d1c64a231c6491d2464a211c64119188492118849192484b192484721046421b1c8491d24849091c849291c6491d0464741188471918841192484b1d24849291c64b1f
|21=>0x2474921046471918849191c842191c84941
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x24c03180330006
|8,0=>0xe551c0a00006e20d751a4a33546428c3517ca2e545a28af5154a2a0851a89e51348255448288b510ca20543ea07850e881bd435286550c2817142ba852509c812542228404076a0d9418a82c504ea08940ea8185
|9,0=>0x3cc87890ef21da43ac87490e721ca438c87090df21ba436c86c90d721aa434c86890cf219a432c86490c7218a430c86090bf217a42ec85c90b7216a42cc85890af215a42ac85490a7214a428c850909f213a426c84c9097212a424c848908f211a422c8449087210a420c840907f20fa41ec83c907720ea4
|9,1=>0x5ca8b8516ea2d945aa8b45166a2c9458a8b0515ea2b9456a8ac5156a2a9454a8a8514ea299452c6a49147228a450c8a0913f227a44ec89c9137226a44cc898912f225a44ac8949127224a448c890911f223a446c88c9117222a444c888910f221a442c8849107220a440c88090ff21fa43ec87c90f721ea4
|9,2=>0x1aea35946aa8d451a6a349468a8d0519ea339466a8cc5196a329464a8c8518ea319462a8c45186a309460a8c0517ea2f945ea8bc5176a2e94
|10,0=>0x83c706ce0c1c153824703ce061c09380c700ce001bfd37f46fdcdfa1bf137dc6facdf41be537c46f7cdee1bd937ac6f4cde81bcd37946f1cde21bc1377c6eecddc1bb537646ebcdd61ba9374c6e8cdd01b9d37346e5cdca1b91371c6e2cdc41b8537046dfcdbe1b7936ec6dccdb81b6d36d46d9cdb21b613
|10,1=>0x9bc736ce6c1cd539a4733ce661cc9398c730ce601cbd397472dce5a1cb1395c72ace541ca53944727ce4e1c99392c724ce481c8d3914721ce421c8138fc71ece3c1c7538e471bce361c6938cc718ce301c5d38b4715ce2a1c51389c712ce241c45388470fce1e1c39386c70cce181c2d3854709ce121c213
|10,2=>0x2781ced39d4739ce721ce13
|11,0=>0xa8254fca9e953b2a7254dca9a95332a6254bca96952b2a52549ca9295232a42547ca8e951b2a32545ca8a95132a22543ca86950b2a12541ca8295032a0253fca7e94fb29f253dca7a94f32
|12,0=>0x15246a40d471a8c35146a20d431
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 15
def pmP:Nat→Nat
|0=>0x13206602620dc04ac338093867012200202408f804805f0089850011200001ec09c02e833805b02700b30ce01642b8029828005301000a445c01441dc0288000050877008000a00e408c01c800802180000330a00062000003c000005cee0007cdc0000df80000ff0000000
|1=>0x1b20ee036419c06c81b80d902701b1c4c03621dc06c43380d883701b1066036209c06c1b300d822701b03cc036029c06c03b80d806701b006e036009c06c01280d802301b000e03540dc06a41b80d44a601a806e03480dc06801380c4850018100002ec00404e41b809a837
|2=>0x1be0ee037c09c06f43b80de82701bc0ce037809c06ec3b80dd82701ba0ee03740dc06e81380dc87701b906e037209c06e03b80dc06701b806e037009c06dc3b80db82701b60ee036c0dc06d81380da87701b50ce036a09c06d03b80da06701b406e036809c06cc3380d9827
|3=>0x20bb04e214808c26c41284d4025092006a0bee1dc17340002dd87705bb0ce0b6e1dc16dc3382d987705b30ce0b6419c16c43382d802705a302008f404011800082200010410000064005c07f83b80ff03701f70ee03ee0dc07d83b80fb03701e6002037e19c06fc1b80df827
|4=>0x21f20ee43e40dc86f83990df06321be04e43781cc86f03390de02721ba04e437019c86e01390db02721b504e43681dc86d03390da03721b404e43640dc86c81390d807721b00ce43600dc86c01390d8023213806e42680dc84cc1b9099077213206e426409c84c0139098023
|5=>0x41be0ce837a1dd06f433a0de07741bc0ce837019d06d033a0d8027415b0008100000c7f83b98f903731bc0e663741dcc6e03b98dc03731b20ce636418cc5c81b98990373120066606408cc0c01192fd02725f306e4b760dc96cc1392b903721fe06e43f40dc87d83b90fb037
|6=>0xc1bd0ef836009f00dc0042f501085bb0ef095c00206f43bc0de83781bb0ef03760de06e43bc0dc83781b904f035200604e400a2fd02745f606e8be209d179c0822de06745b30ce8b6009d164013a2bf0104540002896009d120000a2300014410002880000107f83ba0df077
|7=>0x62fd050c5f50a18b720df16d413e2d9027c5ab0218a7a043140000e210001
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x1020304
|8,0=>0x1912c205ab1a3b0b6c6a7f800c6d0856336b7b0a7d0f35068e23a91d7c172809850daa6ab6881b0e1c107e847b
|9,0=>0x402d9cdca2411362d232862ea76193544339ddc4b75f6e4b373441b1169bb2c72cc5a32b3d1f2e5b5b255b25ba53545f214b6f2539c584de2ae0b4414141185db92d2e4479814bad4a99628999d115b522871e4d5014c924a5ae54485b5f2e623de13e474061594d52c69f2ea8ac2c41d359632e1129c32b4ba45d5b6259da61
|9,1=>0x4d92b327529d710720a12e97c32ee026a6545d493e725760254f38c7619a
|10,0=>0xd53c83655bce555736587340785342a5d6cc52bcd4be412ebfe84e694a7691993c70437a46975582c8e54adfb0515c5e44579e53e2683699af3936733d4e7440d98fd5cd384bca903c649466a077989646e65550d4426442bbbbbb5354483ac13f4f4c524e6446d767b8cb55753e73e72e3665d0e44a99db748cd4953ce346cf
|10,1=>0x45bc48bdc0d8
|11,0=>0xd44a403c73363dbb553c4e4f526439363ed48a434964954e44bb738b53388fbb73424231468d5a50
|12,0=>0x304289362f3c4e
|13,0=>0x2e
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_246 10 roots_246 ops++addP pm 4 dom_63 9 roots_63 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_215 9 roots_215 ops++addP pm 7 dom_182 7 roots_182 ops++addP pm 8 dom_190 10 roots_190 ops++addP pm 9 dom_158 7 roots_158 ops++addP pm 10 dom_222 10 roots_222 ops++addP pm 11 dom_183 8 roots_183 ops++addP pm 12 dom_159 8 roots_159 ops++addP pm 13 dom_95 8 roots_95 ops++addP pm 14 dom_119 8 roots_119 ops++addP pm 15 dom_127 11 roots_127 ops++addP pm 16 dom_247 11 roots_247 ops++addP pm 17 dom_31 5 roots_31 ops++addP pm 18 dom_191 11 roots_191 ops++addP pm 19 dom_223 11 roots_223 ops++addP pm 20 dom_231 9 roots_231 ops++addP pm 21 dom_151 6 roots_151 ops++addP pm 22 dom_221 10 roots_221 ops++addP pm 23 dom_243 10 roots_243 ops++addP pm 24 dom_187 10 roots_187 ops++addP pm 25 dom_87 6 roots_87 ops++addP pm 26 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 45 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 158 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 30 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 158 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 134 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 6 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 134 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 40 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 40 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 7 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 7 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [4, 3] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.or, inputs := [5, 1] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.or, inputs := [4, 12] }, { op := GateOp.or, inputs := [10, 0] }, { op := GateOp.or, inputs := [9, 1] }, { op := GateOp.or, inputs := [0, 11] }, { op := GateOp.or, inputs := [9, 3] }, { op := GateOp.and, inputs := [14, 13] }, { op := GateOp.and, inputs := [16, 17] }, { op := GateOp.and, inputs := [8, 15] }, { op := GateOp.or, inputs := [18, 19] }, { op := GateOp.or, inputs := [21, 20] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52986_aux

theorem PEqualNP.Outside.L_meta_52986 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52986_aux.main
