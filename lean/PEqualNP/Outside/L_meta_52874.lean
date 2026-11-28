import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52874_aux
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

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffefffeee00ee00fffefffeee00ee00fffefffeee00ee00fffefffeee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefafa0000fefefefefafa0000fefefefefafa0000fefefefefafa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaaa00fffafffafafaaa00fffafffafafaaa00fffafffafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffefefaee00fffefffefefaee00fffefffefefaee00fffefffefefaee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfff0fff0fff0fff0aa00aa00aa00aa00fff0fff0fff0fff0aa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffccccaaaa0000aaaa0000ffffccccffffccccaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffff0f0fffff0f0fafa0000fafa0000fffff0f0fffff0f0fafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcf0f00000f0f00000fffffcfcfffffcfcf0f00000f0f00000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffccffffffcceeaaee00eeaaee00ffffffccffffffcceeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffff0fffffff0fafaaa00fafaaa00fffffff0fffffff0fafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_100 : Nat := 0x11000000110000001100000011
def goal_100 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_100 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffff0f0f0f0fafafafa00000000fffffffff0f0f0f0fafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffffcfcfcfcfcfcfcfc00000000fffffffffcfcfcfcfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffff00ff00ffaaffaaaa00aa00ffffffffff00ff00ffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffccffccffcccc00cc00ffffffffffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffccffccffeeffeeee00ee00ffffffffffccffccffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0fff0fff000000000fffffffffff0fff0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffff0fff0fffafffaaa00aa00fffffffffff0fff0fffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffffcfffcfffcfffccc00cc00fffffffffffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccccccc00000000ffffffffffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffcccceeeeeeeeaaaa0000ffffffffffffcccceeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f0f0f0f0f00000fffffffffffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffff0f0fafafafafafa0000fffffffffffff0f0fafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcfcfcf0f00000fffffffffffffcfcfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffcfcfefefefefafa0000fffffffffffffcfcfefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff00ff0000000000ffffffffffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffff00ffaaffaaaaaaaa00ffffffffffffff00ffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffffccffccffcccc00cc00ffffffffffffffccffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffccffeeffeeeeaaee00ffffffffffffffccffeeffeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffffff0fff0fff0f0f00000fffffffffffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffff0fffafffafafaaa00fffffffffffffff0fffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffffcfffcfffcfcf0cc00fffffffffffffffcfffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffffcfffefffefefaee00fffffffffffffffcfffefffefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffccffccffccffccffccffccffccffccee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0aa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffccccaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffccccccccffffffffcccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffccffccffffffffffccffccffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccccccc00000000cccccccc00000000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffccccffffffffffffcccceeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffff00ffffffffffffff00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffccffffffffffffffccffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffff0fffffffffffffff0fffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffcfffffffffffffffcfffefffefefaee00fffefffefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffccee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0aa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffccccaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0fafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00aaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffcceeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccceeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0fafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0fffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffcfffcfffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffcfffcfffefffeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffffff0000aaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffffcccceeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffffffff0f0fafafafafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffffffcfcfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffffffcfcfefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffffff00ffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffffccffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffffccffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffffffff0fffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffffffcfffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffffffcfffefffefefaee00
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
def isoMvS_42:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_41
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_98:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_41
def isoMvS_100:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_100:Lower true dom_100 roots_100 goal_100 4:=lower_iso_b isoMvS_100 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_41
def isoMvS_194:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_41
def isoMvS_196:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_41
def isoMvS_200:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_41
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
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_slice_b [(0x303000003030,32,36)] (by decide +kernel) lowS_41
namespace S_106
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(8,10),(8,40),(8,72),(32,34),(32,40),(32,96),(64,66),(64,72),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_106.map (·&&&dom_106)
def gM:=goal_106&&&dom_106
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x25a8e15ae407a8e
|4,0=>0x71a6b39bad26d910e2a2098a008ad707995
|5,0=>0x9f91c1b19f04f10
|6,0=>0x9f91c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x282800002828000028280000000505000004040000050500000404a0a00000a0800000a0a00000a080000000141400000000000010108080000080800000808000000050500000000000005040000000020200000202000002020000020140000001400000014000000140282800002828000000000000000404000004040000040400000404a0a0000000000000a0a0000000141000001410000014100000141282800002828000028000000280505000005050000040400000404
|_,_=>0
def sP:Nat→Nat
|0=>0x36453645d364531645d360432605d3164c3265b3645364a536495864536753210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 14 107 0x7ffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x355955454d46515654d5644d156551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x82624222000000
|5,0=>0xb1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfa76530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0xab600
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_104 4 roots_104 ops++addP pm 1 dom_98 4 roots_98 ops++addP pm 2 dom_74 4 roots_74 ops++addP pm 3 dom_42 4 roots_42 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_106 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_104 4 s (0,roots_104.map (·&&&dom_104)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_106 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_104 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_106==dom_106)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_106 gM v ys):RunD true dom_106 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_106 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_106 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_106 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_106 roots_106 goal_106 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_106
theorem lowS_106:Lower true dom_106 roots_106 goal_106 7:=S_106.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_46:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_45
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_45
def isoMvS_60:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_27
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_45
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_45
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_45
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_45
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_45
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_45
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_43
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_43
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_45
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_45
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_45
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_45
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_27
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_45
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_45
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_45
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_45
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_43
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_106
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_45
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_45
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_45
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 7:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_106
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_43
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_45
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_106
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_43
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 7:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_106
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 7:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_106
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_106
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xaaaa0000aaaa,8,9)] (by decide +kernel) lowS_46
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,16,17)] (by decide +kernel) lowS_54
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0a0000
def gsh_43_16:=0xf0e00000e0a
theorem lowS_zo_43_16_42:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (lower_slice_b (T:=gsh_43_16) [(0xa0a00000a0a,0,1)] (by decide +kernel) lowS_42)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(8,9),(8,10),(8,40),(16,17),(18,19),(18,26),(18,50),(24,25),(24,26),(24,56),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_59.map (·&&&dom_59)
def gM:=goal_59&&&dom_59
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x116aa
|5,0=>0xa6f0
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f000f00c0c0c0c0c0c0c0cf0f0f0f00000000f0f00000f0f0000f000f000f000f00a0a0a0a0a0a0a0a303030303000300
|_,_=>0
def sP:Nat→Nat
|0=>0x8d53a354c688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x89
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
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dzo_43_16 5 roots_43 ops++addP pm 3 dom_43 5 roots_43 ops++addP pm 4 dom_42 4 roots_42 ops++addP pm 5 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_59==dom_59)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 gM v ys):RunD true dom_59 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_59 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_slice_b [(0x3030303030303030,16,20)] (by decide +kernel) lowS_57
def dzo_46_16:=0x5555000055550000
def gzo_46_16:=0x5554000054500000
def gsh_46_16:=0x555400005450
theorem lowS_zo_46_16_42:Lower true dzo_46_16 roots_46 gzo_46_16 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_16) [(dom_46,16)] (by decide +kernel) (lower_slice_b (T:=gsh_46_16) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
namespace S_62
def pG:List (Nat×Nat):=[(2,10),(2,34),(4,20),(4,36),(6,14),(6,22),(6,38),(8,10),(8,40),(12,14),(12,28),(12,44),(16,20),(18,22),(18,26),(18,50),(24,26),(24,28),(24,56),(32,34),(32,36),(32,40),(48,50),(48,52),(48,56)]
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
|4,0=>0xae7d077c2a
|5,0=>0xf6ea34f5852440f
|6,0=>0xaaa4e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aa22aa22aa22aa25555555544444444aa00aa00aa00aa00444444440000000002a802a802200225555555500000000aaaa0000aaaa000154015401100110028282828282828284444444444444444
|_,_=>0
def sP:Nat→Nat
|0=>0x437104397108437104371064310543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 63 0x7fffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x103
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_46_16 5 roots_46 ops++addP pm 3 dom_42 4 roots_42 ops++addP pm 4 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_54 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_46 5 s (0,roots_46.map (·&&&dom_46)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_62 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
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
|0,1=>0x2aaa8000000000000000555555550000000050505050222222220000000000000000141414140000000014140000000002a8000000000000000555555000000000055555500aaaaaa000000000000000001555511100000000155551112aaaaaaa8000000022222222555555550000000055555500
|_,_=>0
def sP:Nat→Nat
|0=>0xcc1410660a0991982820cd80a0921982820cc1892e91991620cc1412a3305049c8660c4901982821828790660a1c41982d41066605043050b21828511260a0e3304a418820
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
|0=>0x1920911a10a6191a10411499191092
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x520041311200000100
|6,0=>0x91008171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffde6878a183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2605430010
|6,0=>0x8789
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_74 4 roots_74 ops++addP pm 3 dom_78 5 roots_78 ops++addP pm 4 dom_86 5 roots_86 ops++addP pm 5 dom_90 5 roots_90 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_94 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_90 _ g hchk
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
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
namespace S_109
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,36),(4,68),(5,13),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,44),(12,76),(32,33),(32,36),(32,40),(32,96),(64,68),(64,72),(64,96),(65,69),(65,73),(65,97)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_109.map (·&&&dom_109)
def gM:=goal_109&&&dom_109
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xf22e7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333000000000000333300000000cc000000cc000000cc000000cc03030000030300000303000003030888800008888000088880000888b333000033330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 110 0x3fffffffffffffffffffffffffff
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
addP pm 0 dom_108 5 roots_108 ops++addP pm 1 dom_45 5 roots_45 ops++addP pm 2 dom_105 5 roots_105 ops++addP pm 3 dom_101 5 roots_101 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_109 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_101 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_108 5 s (0,roots_108.map (·&&&dom_108)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_109 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_108 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_109==dom_109)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_109 gM v ys):RunD true dom_109 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_109 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_109 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_slice_b [(0x220022002200220022002200220022,16,17)] (by decide +kernel) lowS_116
theorem lowS_122:Lower true dom_122 roots_122 goal_122 8:=lower_slice_b [(0x5050000050500000505000005050000,64,80)] (by decide +kernel) lowS_106
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_slice_b [(0x4400000044000000440000004400000044000000440000004400000044,32,34)] (by decide +kernel) lowS_228
namespace S_234
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(8,10),(8,40),(8,72),(8,136),(32,34),(32,40),(32,96),(32,160),(64,66),(64,72),(64,96),(64,192),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_234.map (·&&&dom_234)
def gM:=goal_234&&&dom_234
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x83d77
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50500000000000005050000000000000505000000000000050500000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a0101000001010000010100000101000001010000010100000101000001012828000028280000000000000000000028280000282800000000000000050500000505000005050000050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 235 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_232 7 roots_232 ops++addP pm 1 dom_170 7 roots_170 ops++addP pm 2 dom_226 7 roots_226 ops++addP pm 3 dom_202 7 roots_202 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_234 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_202 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_232 7 s (0,roots_232.map (·&&&dom_232)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_234 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_232 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_234==dom_234)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_234 gM v ys):RunD true dom_234 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_234 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_234 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_234 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_234 roots_234 goal_234 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_234
theorem lowS_234:Lower true dom_234 roots_234 goal_234 9:=S_234.noCircuit
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_61
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_61
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 8:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_107
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_61
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_109
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_117
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_109
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_61
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_61
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 8:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_94
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_109
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_107
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_61
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_109
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_117
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_122
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_109
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_122
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_59
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 8:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_107
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_59
def isoMvS_213:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_122
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_107
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_117
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_107
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_107
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_122
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_122
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_107
def isoMvS_236:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_230
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_117
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_107
def isoMvS_244:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_230
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_107
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(24,56),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf1020923f59089f6129a2d780
|5,0=>0xe2aafdfcf6d9245cdbbcca973bc4f1b08c8a544199818971348e1da428452133316de40ba3d
|6,0=>0xf47e6e62f6ddd8bdd808cf6b2cf246bad5eb52c4b40d5b30d0b17a7a528aa43039c2ed9ba9c96bec91e73908be8e1da888bc84f7c7c4e3785bc758e072b0e692a4664126324a5ce5b5a9d24d95439e342b5df2b4e3241930779704701
|7,0=>0xf8293dd808d42517adc35f7114f362414e64017b29ed429720
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff33ff33ff00ff0000000000ffff000033333333000000003300330033003300ffffffff00000000ff00ff00ff00ff00fefefefefefafefaeeeeeeeeeeaaeeaaffaaffaaaaaaaaaa333333333300330000ff00ffff00ff00ffffffffff00ff00ffff0000ffff0000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0033003333003300
|0,1=>0xccccccccffccffccffff3333ffff0000ff000000ffff0000cc00cc00ff00ff000000000033003300ffccffccccccccccffffffff33003300ffffffffccccccccffccffccffccffcc00000000ffccffcccccccccccc00cc0000ff00ff0000000000000000ff00ff00ccccccccccccccccff00ff0000000000ffffffffffff0000
|0,2=>0xfff0fff0f0f0f0f000ff0000ffff0000ffffffffffccffcc00cc00ccccccccccffffff00ffff0000ffff00ffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x48158b0ca09205b1180ca0920440da08164328204d1180d708140a0920561031c24842c32822040c248114b0ca0880c24811440d108118b0ca0811902ca08118b0cf08130b2820463840c204d30b0ca2481031c21830811400c20461440c2040
|1=>0xca0920464042ca0920430920544cb0ca0811902ca0920532e12824812e028248164b0ca09204b0ca09f4812c368a08160b0d72820442ca09204e2c33ca09204b2824813932c31ca09210328248134b78a09204b29d09204b0ca0927012c3282
|2=>0xca09204d2c35ca09204b0ca0920542c32824813102d728248110b0ca0950502ca09204c10b0ca0920440d109204b0ca0950442c35c24812c394a4812ca0920648cb0ca09204b0d709205310b0ca0811842c309204c2c32820622c328204d30b
|3=>0xb0ca0920582c328248110b0ca09204b0ca09205340b2824812c329109204b28248138b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94c8c5e62c314d49ac4762128f546ec31615b09583ec196
|6,0=>0x15e7abbd41e92f4369eb4d9e60d2a691bc71e2af0e7843405df4ef3776b39d9c0eda66a3335d8cec065cbac9d56ea474f325dd22c8b64239f5cece6f7
|7,0=>0x344f9b7ca3e39b0ef816bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb492ca4b2a2c34b282c38b4b2924b2b292cb0d2c34b292ca04482ca4b294424b280d1cb282ca8b292ca514a2ca0b2b2ca844b2ca43452ca03512cad1492ca0b294414b282ca43352d2c3532caca372ca4b294524b282ca4b294414b2854144482ca544d2cacb2a
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa30009100063000000cc03000000000000000
|6,0=>0x301002f1002d2acaa1a0a62002519063184800000007c9d2001b26480000172001610000050931448f238400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf3fcde7e689060b8120277ddd73d8d6258114450110421002a07c1a0180400c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc050204230c0000000
|6,0=>0x511296396ee010956800ab852e7801713009c2e0e58005
|7,0=>0x27ad477296779
|8,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_29 4 roots_29 ops++addP pm 2 dom_61 6 roots_61 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_54 4 roots_54 ops++addP pm 6 dom_31 5 roots_31 ops++addP pm 7 dzo_47_16 6 roots_47 ops++addP pm 8 dom_47 6 roots_47 ops++addP pm 9 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 7 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_122
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(32,96),(48,49),(48,52),(48,56),(48,112),(64,68),(64,72),(64,80),(64,96),(65,69),(65,73),(65,81),(65,97)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xa26198cc463c30f
|6,0=>0x51f8c4c6b22f9741c6be1abd9
|7,0=>0xcf815c675774b3a4624f
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33303330333033303330333033303330cccccccccccccccccc88cc88cc88cc8b3333333333333333300330033003300cccccccccccccccccccccccc8888888b3333333333333333333333300000000888888888888888888888888888888883030303030303030303030303030000cccccccccccccccc00000000000000033330000333300003333000033330000cccccccccccccccccccccccccccc00033333333333300003333333333330000cccccccc00000000cccccccc000000033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333332222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x36219736210736c2197a36219736e219736d21074a219743210736c210b3621074a210432987543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x31433006
|6,0=>0x2a748c798c3117
|7,0=>0x8ccfddc3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x25d274dd2165d635cd3665d9749d9758d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|6,0=>0x8162422211
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x8a02fcd5e67d31f9806000c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x28ef
|7,0=>0xcdb
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_57 5 roots_57 ops++addP pm 2 dom_45 5 roots_45 ops++addP pm 3 dom_116 5 roots_116 ops++addP pm 4 dom_117 6 roots_117 ops++addP pm 5 dom_121 6 roots_121 ops++addP pm 6 dom_85 5 roots_85 ops++addP pm 7 dom_61 6 roots_61 ops++addP pm 8 dom_93 6 roots_93 ops++addP pm 9 dom_109 7 roots_109 ops++addP pm 10 dom_77 4 roots_77 ops++addP pm 11 dom_60 4 roots_60 ops++addP pm 12 dom_92 5 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_125 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_125 roots_125 goal_125 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_125
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=S_125.noCircuit
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,56),(24,88),(32,34),(32,36),(32,40),(32,96),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xedae3
|7,0=>0xa64696dfc85e57f5374b23990
|8,0=>0xe29657e995
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x15555555555555555551155115511551002a802a802a802a8022002200220022555555555555555500000000000000008888888888888888888888888888888954015401540154015401540154015402aaaaaaa800000002aaaaaaa8000000055550000555500005555000055550000aa88aa88aa88aa88aa88aa88aa88aa8955555555555555555401540154015402828282828282828282828282828282855555555555555554444444444444444
|_,_=>0
def sP:Nat→Nat
|0=>0x5461785436178546107854a6107854a6178546179854261075432178543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x2286dd4735c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19d78581784e167582785a1785a1765e1685d9
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
|7,0=>0x6f2b
|8,0=>0x14
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 8 roots_122 ops++addP pm 1 dom_124 7 roots_124 ops++addP pm 2 dom_118 7 roots_118 ops++addP pm 3 dom_62 7 roots_62 ops++addP pm 4 dom_94 8 roots_94 ops++addP pm 5 dom_110 8 roots_110 ops++addP pm 6 dom_116 5 roots_116 ops++addP pm 7 dom_54 4 roots_54 ops++addP pm 8 dom_60 4 roots_60 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 8 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,28),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(64,66),(64,68),(64,72),(64,80),(64,192),(128,130),(128,132),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|4=>8
|5=>45
|6=>181
|7=>132
|8=>31
|9=>6
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3d858239be232f01e84611d6b0e6b10ac7502cbc
|5,0=>0xc3de07881372db56ceef67314620bb565d24b80649f093dac83b5a23835735bed320e02de882d1922c85229e6f25a1725810256cd2478423d9a202931f89f1c70e1bee518f2a18a64174b5161b5147a8145640fa900bc3b0b9cc0b65509cd9091b0075ec064930586605089041ec02831
|6,0=>0x398bb3810737bc636dfd3637e35f6d34c2134202336cc32a43326ea321113150830cc12f5992f0902df902d5282c3202b9ae2b6ab2addf29e2427e20276522690b250a224a8223c8a23a71226b22256121f1d21d14218332060c1fc211ed881e59f1da151d9891d7ae1ce821cb601c0821ba7c1aeab18e8f186c9181f9181d217b2c17734170cb16f9216ed716bc7157a01495213f7913d9713cb512a8c12421121011190c1137310f0a1083c104de101840ffb70ffa30ff540fbc30f87d0f3010f2590ef3e0e9e60e5bf0e2440db7f0d95e0d6f00d3700cbfa0c3590bf050b5780b2f30ae5f0ad7a0acdb0aa710aa6e0a8d60a7140a37309cdc089c30895508723086e5086b90813c07f65071d10703b0618a05521052b90505504b3d040ad03eb40302402a1d02831024ae02246017e9013d0012df00ff000522003ce00222
|6,1=>0xc3de09c11e8f22487e7886de5847b983ab78137379ba0769c075506737ff6ef8c671d86438263e3062dd6606665f4605eeb95bece5af1e57cdf5704955ca7559d5559805502c547275181b4f7414b8a64ab6c47a2446578455b64522443d434298a42074416ab412a840ab33fda43fcf33f6833f0f13ded43d3b63d2433a77239d6d39b51
|7,0=>0x7605873c646d7e36b9fa6ad1b69b9d6787265d025eac75149650a624c3ce4aeab4ae0e4a8ed478f3458054556d453594489b444273e2923d2d53cfe83c4e83bee438c7f38c39387d4378b437741356c8355813541234a68335dc32d77327ed3264831a88310652fa342f0352ea592e07b2de5a2c62d29fd12905e28fca28e5b287262769126f672566b236d92334722561223a02183320b1f2043c201151ff361fbb31f5eb1ef971e1d41de121cc6c1c58d1b09e1af1c1ae691acb51968818cb8187a918423180d316444164031632a1620b15f0f15dc11592a14740140e4136281303b12c531299e1298d11fc211991118f310cce1015b0fc980fc000df7a0cf520cced0be0f0b1c30ad530a6900a3ee09dd209aae08ee907a80067b6065bb0651d0609d05e5c05a59058e90581b045ab04112037e702de402048008d100208
|7,1=>0xb09089c09c846d17d633
|8,0=>0x962ab88d1354b97500464b6a54a5a84a23448f353e10d3a41531a9429ee0276692680925d1c24f0e24bd61cad115662149d80ead10e24c0dec70de0e0cc540be1a0a8130882406328054ff02b63
|9,0=>0xbad5e62fd6577e12b37d05964050df
|10,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa00000000aa00aa0000000000aaaaaaaa00000000aa00aa0155555554000000015555555400000001555555540000000141414142aaaaaaa800000002aaaaaaa800000002a802a80000000002a802a8055555555000000005555555500000000555500000000000055550000aaaaaa8800000000aaaaaa8800000000aaaaaa88000000008888888955540000000000015554000000000001555400000000000155540002828282800000000282828280000000028282828000000002828282855555500000000005555550000000000555555000000000000000000aaaaaa0000000000aaaaaa0000000000aaaaaa0000000000aaaaaa0155555554000000015555555400000001555555540000000000000002aaaaaaa8000000000000000000000002aaaaaaa800000000000000055555555000000005555000000000000555555550000000055550000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa00aa0155555540000000015555554000000001555555400000000141414142222222200000000222222220000000022222222000000002222222255555555000000005555555500000000000000000000000000000000
|0,1=>0xaa00aa0000000000aa00aa0000000000aa00aa0000000000a800a800015554000000000001555400000000000155540000000000015152aa82aa8000000002aa82aa8000000002aa82aa8000000000000000055554444000000005555444400000000555544440000000000000000aaaa888800000000aaaa888800000000aaaa888800000000aaaa888955555510000000015555551000000001555555100000000154015402aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002222222200550055000000000055005500000000005500550000000000550044aaaaa8a800000000aaaaa8a800000000aaaaa8a800000000a0a0a0a155555554000000011111111000000001555555540000000111111112aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaa800055555555000000005555555500000000505050500000000050505050aaa8aaa800000000aaa8aaa800000000aaa8aaa8000000008888888954015400000000015401540000000001540154000000000154015402aa82aa8000000002aa82aa8000000002aa82aa8000000002aa82aa855555550000000005555555000000000555555500000000055550000
|0,2=>0xa8a8a8a800000000a8a8a8a800000000a8a8a8a8000000000000000151515150000000015151515000000001515151500000000151515152aaa2aaa000000002aaa2aaa000000002aaa2aaa000000002a802a80000000000000000055555555000000000000000000000000555055500a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a000a0000014544000000000001454400000000000145440000000000014140022002a800000000022002a800000000022002a8000000000220022111111110000000011111111000000001111111100000000111100000000aaaa000000000000aaaa000000000000aaaa000000000000888955555554000000014141414000000001555555540000000141414142aaaaaaa800000002aaaaaaa800000002222222200000000222222220505010100000000050501010000000005050101000000000505000000aa00aa0000000000aa00aa0000000000aa00aa000000000088008800015554000000000001555400000000000155540000000000014140282800280000000028280028000000002828002800000000282800000000000000000000505050500000000111111110000000000000000
|0,3=>0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a00015554015400000001555401540000000155540154000000015554000002a802a80000000002a802a80000000002a802a800000000000000011111111000000001111111100000000111111110000000011101110000a000a00000000000a000a00000000000a000a00000000a0a0a0a04404440400000000440444040000000044044404000000004400440000028a880000000000028a880000000000028a880000000000028a8111111110000000011111111000000001111111100000000110011000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a000404040400000000040404040000000004040404000000011111111002a802a80000000002a802a80000000002a802a800000000028002800001111000000000000111100000000000011110000000000000000aaaaaaaa00000000aaaa00000000000088888888000000008888000115151514000000011515151400000001151515140000000111111110282828280000000028282828000000002828282800000000000000000450045000000000045004500000000004500450000000000440044
|0,4=>0x202020200000000020202020000000002020202000000000000000155540154000000015554015400000001555401540000000155540110000000000000000028282828000000000000000000000000202020250505050000000005555555500000000505050500000000054545454aa00aaaa00000000aa00aaaa00000000aa00aaaa00000000aa00aa0155555554000000015555555400000001554155400000000155415542aaaaaaa800000002aa82aa8000000002aaaaaaa800000002aa82aa855555555000000005555444400000000555555550000000055554444aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaa888955555554000000015555555400000001555511100000000155551112aaaaaaa8000000028282828000000002a802a8000000000280028000000555500000000000055550000000000005555000000000000000000000000000000000000000000000000aaaaaaaa00000000aaaa888800000000000000015555555400000000000000000000000155551112a82aa82800000002a82aa82800000002a82aa82800000002a802a8050555055000000005055505500000000505550550000000050505050
|0,5=>0xaaaaaaaa00000000aaa0aaa044444444000000004040404000000000444444440000000040404040888888880000000088888888000000008888888800000000808080811111111000000001111111100000000111111110000000011111100aaaaaaaa00000000aaaaaa0000000000aaaaaaaa00000000aaaaaa015555555400000001555555540000000155555554000000015555540000000000000000000000000000000002aaaaaaa800000002aaaaa800055005500000000005500550000000000550055000000000055000022222222000000002222000000000000222222220000000022220001555555540000000155555554000000015151515000000001515151502828282800000000282828280000000028282828000000002020202555555550000000055555555000000005555555500000000555055500000000000000000000000000000000000aa00aa0000000000a000a154015400000000015401540000000001555555540000000155415540888888880000000088888888000000008888888800000000000000051515151000000005151515100000000515151510000000050505050
|0,6=>0xaaaa888800140014000000000014001400000000001400140000000000000000282828280000000028002800000000002828282800000000280028050555055000000005055505500000000505550550000000050545054000000000000000000000000000000000000000000000000aaa0aaa1555555540000000155555554000000000000000000000001554155400028002800000000002800280000000000280028000000000028000555555550000000055555555000000005555550000000000555555000000000000000000aaaaaaaa000000000000000000000000a8a8a8a9555555540000000154015400000000014141414000000001400140000002aaa8000000000002aaa8000000000002aaa8000000000002aa811001111000000001100111100000000110011110000000011001100000000aa00000000000000aa00000000000000aa000000000000000155555554000000015151515000000001555555540000000151515152aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002a2a2a2a55555555000000000505050500000000555555550000000004040404
|0,7=>0xaaaaaaaa000000000000aaaa00000000aaaaaaaa00000000000088880000000000000000000000000000000044444444000000004444000002a802a80000000002a800000000000002a802a80000000002a8000000500050000000000050005000000000005000500000000000400048888aaaa000000008888aaaa000000008888aaaa000000008888888955544444000000015554444400000001555444440000000155540000000282a800000000000282a800000000000282a800000000000282800000000000000000000000000000000005500550000000000550000aaaaaaaa00000000aaaaaaaa0000000000aa00aa0000000000aa000000000000000000000000000000000000000000000000000155555402aaaaaaa800000002aaaaaaa8000000000000000000000002aaaaa800000000000000000555555550000000000000000000000005555550000000000000000000000000000000000aaaaaaaa00000000a8a8a8a8000014140000000000001414000000000000141400000000000000000002aaa8000000000002aaa8000000000002a800000000000002a8055555454000000005555545400000000555554540000000055550000
|0,8=>0xaaaaaaaa000000000000000000000000aa00aa0044444444000000004444444400000000404040400000000040404042aaaaaaa800000002aaaaaaa80000000002a802a8000000000280028000000000000000000000000000000000000555500000000000044440000000000000000aaaaaa00000000000000000000000000aaaaaa0001540154000000000140014000000000015401540000000001400142aaaaaaa800000002a802a80000000002aaa8000000000002a800000000000000000000000000000000000005555444400000000555544440000000000000000aaaa8888000000000000000000000000aaaa888800000000000000000000000000000001554155400000000155415540000000000000000000000000000000008888888800000000808080800000000000000005555555500000000000000000000000044444444aaaa000000000000aaaaaaaa00000000aaaa000000000000aaaa88880000000000000000000000000000000014141414000000001400140002a802a80000000002a802a8000000000280028000000000028002800005555000000000000555500000000000044440000000000004444
|0,9=>0x155555554000000011111111028282828000000002828282800000000202020200000000020202020055005500000000005500550000000000550000000000000055000000000000000000000000000000000000aaaaaaaa00000000a0a0a0a000000000000000015151515000000000000000000000000151515152aaaaaaa800000002aaaaaaa8000000000000000000000002a2a2a2a00000000000000000000000000000000555555550000000055005500
|_,_=>0
def sP:Nat→Nat
|0=>0x2c12012b001209162a05000c09012905001209282705000a12261306000c121701050a12252406050901232205000a0d012106050a120901062009011f1e05000a031401051d0a1a09190500150d090105080a09011805000403090b000c12171606150d090b050a0f141306100f0e0100040d090b060c03090b050403020100
|1=>0xc120938060a0f0d013f060a2d260106000a030121050010120e01050012093c2205000a123b0105000a12143a06051209383905000a12383705000a12093605000a03020105000c1a090106050a2c090135000412092506341b120933060c120201050a1214162f0a0e013005000a2d092506050a03091305000c0f0901080a
|2=>0x12206050a492c120901000a0901180500470a0901230500151209010534000a0f0d0e09010648430a1209250543460a120901050a1112400105000a11450105000c120916010644070c03090106050a12093c050043420a1209010a4140010500151a090105000a121416062f0c0f090106080c1217010605100f0901060004
|3=>0x5806050c12090157060a1256015505000a5412012b05000a520d090105000a1225013f06051b0c120916060a1226012b06000a125001054f00040a09011805000a1112012b05000a0f12013f0600150a0f0d0901060a122e2625064e0a09012305000a124c26010500041209011c00154b12090105001b1512092506050d1209
|4=>0x1000a12093c0605000a5f120e090105070a4b09010500431b0c120901050a4a12260106121401220531000a1214015e06071509015805000a122e0e5d05004604120901060a0f12095c0500590a12090106055b070c120901060a09013005000a0f0d090106310a490901350500590a0d120901050a0f40090105000a0d0901
|5=>0x640544000a120925054f005b0a12013f0500126109012205000a0d09010605080a0d09010605630a122e0e1905000a1262095d05000a1201370605000a1226015505001b0c12091906050a0d12013705000a0312095c05000a1226090160000a495f120901060a1226320105000a0340090105000a1256261401060a542c1209
|6=>0xa0d260901063d0c12090106051c040a090123060042040a120901000a12013f6905000a0d0938053d00541209016505001b0a092523050068070a0f090106680a12013705000a1256670901060a12096601060a540901350500111209016505001b0412092805000a1109013505000a110f0e0106001b1209162705000a1209
|7=>0x12013f0572000a1209165d05000a110e013505000a0901232705001012090105000a122e265d05000a0f09017106701209010605000a120901054f003e0a0d090106050a620901230500470a12090105000a0d090106056e0a0d09016d060a0901230544000a1226011d000a6c09012305000a6a12090106053e120901056300
|8=>0x60a491209380500430a12091601060a12732e0925050a120e01054f000a410901056e000a110d093805000a09192305510012090122053d00150a09012305005a590a120901050a1226140106510a4a12093c0500120e01220572000a0e09012305000a490d2609010659040c120901050c1209010534000a12562e09160604
|9=>0x1901060a2e09011f05000a0309010508000a030901056300590a0f120901060a1267140901060a120916061c000a4112093a05000a0d1209017705041209010563005b590a0d0901050a125001053100750a1209010605740c0a120901060a0309015805000a12500916060068040c120901060a0932013005000a1256262501
|10=>0x500150a12013705000a4a0d1226010674040c120901000a12013f58050059150a120901050a0901300605000a121401051d0a120e093c050048460a120901061b1512013f05000a12621401060a4112260106001512013f0544000a12097b0551007a0a12012405000a12562601061209017905000a122601066e000a122614
|11=>0x62091625060a490f0d0901060a5f03120901050a4912261401060c0a120137050074150a120901000c12097b0106050a12670e09010048430c1209010511122601220500070a03093805000a0901237c050015120901051c00071512013f05000a12730e0901050a1273091625050a1209195d0500480a1209250611120e0122
|12=>0x5b590a12090105000a1209017f05000a122e0e14010500740a0d12090105006f0a12090105000a2c0d120901050047460a12090105000a122e14010605120e09012206050068040d12090105000a110f09010600680a0f0d090105000a1209017e05000a1209017d06000a122e091905000a12093c0500150a12095c05000a12
|13=>0x9010551000c0a12090106053d0a12090106053400040a1209190106000a120925018505000a120e26010531000a120e09010551000a091916012305001b0a120919250500830a1209010500070a03090105000a12090106052f000a1214090182050046040c12090105000a1226018105000a12091625060a12097b01054400
|14=>0x605440a120901055131000a12140901350500870a12092505000a860f090105000a120901800605680a0312090105000a126209190105000a12612e090105000a1226092501060a12090105446300480c12090105000a122e141605000a12091901054400470a1209250105000a4b1209010605000c0a031209010605150a12
|15=>0x1250090105000a120e0919010500460a1209250106050a1209018c05000a12093805008b0c12090105000a1214018a0500150a12013f05000a4912140105000a4a0f0d090105000a120e09015d050059070a12090105001b0a12091905000a1209160551000a120919012705000a128909010500880a12091605000a0d120901
|16=>0x48040a12090106000a12622e09010600481b0a12092505001209012205000a120901280605000a54120901060500480a12090106000a120901051c0047040a12090105000a0d120e090106050a0f12093805000a1209168005000a120901054f0015040a12013f0500470a12090105000a1226018e05000a1209018d05000a
|17=>0xa11120e010605005b0a0d090105000a1291090105000a127326090105000a12092501270500070a90090105000a12610e090105000c1209010605445a0a0312090105000a1262092505000a12090155060500070a8f090105000a12560919010500070a1209010563000a121401060531460a12090106050a4a0312090105
|18=>0x10605000a1209013505005b070c12090105000a122e09190605000a1209019406050a1209017106050c0a12013f05000a122e262505000a1112930105000a0d090106053d0a1209012705000a491112140105000c0a0f120901065b040a0d090105000a122e0e0105000a494a1209010500150c1209010544000a5f12090105
|19=>0x5070a0f090105000a1112260105000a1209015e05000a120e01060531000a120919060551000a12097b0105000a1226010531007a0a1209010500120901220605000a12261401060a490d26090105000a125009010605000a120938060500150a12013f0605000a120e010531000a1240090105000a1209190551006f0a1209
|20=>0x461b0a12090105000a111209010605000a12561409010500040c12090105000a4a1209010500870a12090105000a122e092505000c0a1209160105000a1214090106050a031209010605000a030d1209010500150c0a12090105000a12090106053d00680a12090105000a120901950500040a0d12090105000c0a12090106
|21=>0xa12090105000a12090105000a1226090105000a1209160105000a122e090105000a1209010605000a0d12090105000a120e09010605000a120901060544000a120901053100150a12090105000a120e090105005b0a0f1209010500480a1209160105000a1209162505000a1209010544000a0f12090106000a1209960105
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x23501e50195014500f500a500550005
|5,0=>0x12b6125611f61196113610d6107610160fb60f560ef60e960e360dd60d760d160cb60c560bf60b960b360ad60a760a2509d50985092608c60866081507b6075606f60696063605e50586052604c60466040603a6034602e60286
|6,0=>0x2e072d972d272cb72c472bd72b672af72a872a1729a7293728c7285727e7277727072697262725c6255724f62487241723b6234722d7226722062197212720b720471fd71f761f071e971e271db71d561ce71c771c071b971b271ab71a5619e71977191618a7183717c7175716f61687161715a7153714c7145713f613871317
|6,1=>0x49b7494748d7486747f74787471746a7463745c7455744e7447744074397432742b7424741d7416740f7408740173fa73f373ec73e573df63d873d263cb73c473bd73b673af73a873a2639b7395638e7387738073797372736b7364735d7356734f73487341733a7333732d6326731f73187311730a730372fc72f572ee72e77
|6,2=>0x609660275fb75f475ed75e675df75d875d175ca75c375bc75b575ae75a775a075997592758b7585657e7577757075697562755b7554754e6547754075397533652c7525751e75177511650b650474fd74f674ef74e874e174da74d374cc74c574be74b774b074a974a27
|7,0=>0x7ea87e377dd67d677cf77c877c177b987b187a987a2779b7793878c7785777d8775876d8766775f775877508748874087397731872a7723771b8713870b870386fb86f386eb86e386db86d386cb86c386bb86b476ad76a5869d8695868e768866808678867176698661865a7652864a8643763b8633862c7624861d7616760f7
|7,1=>0x9c579be79b869b089a889a179998992798b7984797c8975796d8965895e7957795079497942793b7934792c8925791d8916790e890688ff78f788f078e978e188d988d278ca88c378bb88b478ac88a5789d8895888e7887787f8877886f8867886168598851884a7843783b8833882c7825781e7816880f7808780177fa77f28
|7,2=>0x9e289da89d379cc7
|8,0=>0xac88ac08ab97ab27aab7aa38a9b8a947a8d7a867a7f7a778a6f8a678a607a597a527a4b7a438a3c7a348a2c8a248a1c8a157a0e7a0689ff79f879f179ea7
|9,0=>0xaf36aec7ae57ade7ad77ad07
|10,0=>0xaf96
|_,_=>0
def wAt:=mkWire dB 151 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x706014010500428052504004010908428010706000150a124b81805004240101054c84b013141401122f404012e0600015011d444181206414011209448150a0041c180500424710a0046c18050042805090044418050044871010646c18050042805120041c180005428150706014010108448010706000151205444180005428010706014010a0542421070600015
|1=>0x10a449110500404010a064140112004283a0906414014a05c441511004644b2505404011b06828190500448150906400151200520030401428154700d1815250a4441a050042449260d0241512004281a010542801120641401121c46c180500424710a0046c1805004040e1206414010a00448011509c28190500424fa0a3d41401090642875110601401120942421
|2=>0x54480112264384b260056803040d428151215828190005428010401c28150005424662509494150f14448151253498370905448010100454270a06414010105414010a004240e1206400155009c25450106814014712c54050400528151100448151509c28190500448151200428190500400150905404011219858010105425352625824150100428151b0600015
|3=>0xd05448014d05498960905404014900c98490905424f50500450050905414010900550170f14448155401c44190912498014900c98490706814011b05428050005424151412424010a0e850150126824010005424151215830150a00438071405424010a25404010005428155a01c303d0a00568030706414010a12414010705428491232804c509068140112054241a
|4=>0x1912c94150100400150700448295605c9425010041401140f024011205448d50e12c50150900429524a05444010400428155412d28151100448150906414011600404150951864072505404010a0e850150900448010706014010a12449120a068140101064241905005880116094256a0706428496109c38052600424150a0040419000556827040d428155a01c0c29
|5=>0xa1d444180500448252600424150500428361205448010a2f4b81805004042512069bc191b06c1401093d8481a0500448010f09c14011205424151106014010912448661600404156b004441b0500424490a3d428f61206814011206824150a0046c180500428051912c28150106400154705c54050400428150915810010a0540c070d055502b260d42415120042805
|6=>0x500424150925404014800c285901054b8150109404c60e09c98010905448c612314241a0500448250301c34151200448661901c94150100448660106414015a00c10350a054241501068140109004248a0e0ac501509004644b010641401120049849090556c030412428150a28854070c054280105004b8010901428fe1509c10010a054505909004483a260042415
|7=>0x400ac24f512068140111068140112094041909054140109004498656054b801120641c18050042849070383415120056c030f0a448155605c50050900404151b06014010a01448c50906814017800410370a0544912150ac10010a0556c030f0a44815090682545010681401760041c1b0005448296805c30490a0040c290d054041a0500448310a004281501314241a
|8=>0x905588031609404150906414010401404010005428150a0e84825260042415095a854490c0542801090d4480109055a017120c428015a00c30150a004c84b01314241a0500424011106014010912405520e12450151b00400151b05428050915828050c054280105004582501054240109068281a1509c281905004281a050042945010681401011441401090042415
|9=>0xa0d448011205410970a05404010412c00150a05458010109404155a01c54490c0540401091641401010540015090f448011205524030f00448151226414010900424155a09c54490c05430156805c28010a06958171405424014800c285901054283a09124980109054040e0f004482912054644b2505404011b06028190500428051509c28490c05428016200c9801
|10=>0x9054041a05004644b160040415250540429010042a112505c0401120a4341512004b818050042405140f848150a05430050a004485209004241505004040101054281a050056c0304124281580054942b0100424051405424016805c2835120046c1b0500404294a05c3425120051815250a4040109014140109004283a0906414010a0d42815120041401120944815
|11=>0x1054281a00054480109068041a05004384b140542401010046c170a014440312094481505004942b0100434290d05448011609458010105558152e00414010905404010a06814010a16428010105424010109404150a06814010425428150100449110a06814010a004481905004041a05004481a0500428011b0681401010a404190005428152625c24150e09c9801
|12=>0x500424051509c10010a05410950a05404010114824010905628012612c241509514041a0500424190106414010a254001501004305a0a00404150301c34151200428010705c28491226824010905454270c05428010900498490905424351205448010e01c5015090056c030705428490a01458010105464071600404150a198580101054303c0a00448151b00c0429
|13=>0x50040c290d05448012601424150100424660106414010d05c4829120049415250940401070681401090681401090041401250a404010d094341512004001504014281500054b815090146c15010a404010a0e898010905454070a06414011106414010912410050005428151b0601401010a45405040042815090640015120040c070f00448150a258041501004b81a
|14=>0xa00414010d0ac00151200454270c054280109014241501004980309124241512068001512004286616004041511054244909004481505004280104124281512004240514054240111054440112094542b0c05428014900c98490905424190500424490705448291200648012e05c24056200c980509054642b2505404010a1243c031205438051405424010a004281a
|15=>0xa0544801050042801120a448150912424152601c241509314241a05004041a01064140101444281a0500438272600424150a514041a05004283a09064140109054140109004480126124241509514041a050040c071206414011509c2819050043827140542401093d4481a0500464071600404151b06c04290e12c501509004280107054284901064140109014304b
|16=>0x24150105424050500448010906414010a06814010906814010c05428012600424150f0a448150a16404150100404150a06814010500448151600c04151b00428050500424491401424010a05428011412424011b05c28050100424050a00404150900414011206414010d05448010c05428011206814010d0a448012509c0401
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x1c60000052000000e600000218004
|5,0=>0x2a980000000145000004d4092800002318415000000000000000000000001f1800000000f441d1835506280b8c1520255042800000000000000000000e28000000000000000000032605140898000
|6,0=>0x22e8450c88990f22186421082990231fc83e907b980001ea43c507718eb31d0639887210e041bc436906b98d431a08334c64a0c6318482f905d98b8300002d4c58a0ae315842a105220a1313c626904b9895212282350451887310681fd03e907a30ec81ccc00007030da61a5033186330c2417502d90583
|6,1=>0x38e47184e121bf337860000dc99b7236686bd0d5a1a740000690cd0999d400006650cb1993332066310c4998543064600c00017c42f445d90b9200002e220000b7196b32ce80000b1a16032b885610ab1152429c85290a39945228284f509d1800026e64cd097a12c3254449cc92192220000479000011b3
|6,2=>0x4e269b5134a26634c4897cd2e1a5b14b06954d28a24d44946919121223f347868e891b2232445c88acd141800044a688510ea21a342c8849107220d1412881c9021a0043f887e4cfaa1f233dc87accf419e533c28778ced99d743a867410e621c93
|7,0=>0x6526c98d919b20363a6c68d8b9b1436226c38d859b08360a6c08d7f9afc35f26bd8d799af035da6ba8d739ae525c46b8096e9ada35b04b54d691acf359a4b28d639ac435844afcd5e92ba356e6ad0d589aae35584aa4d531aa335424a78d4d9a98352a6a48d479a8c35126a18d419a8034fa69e8d3b9a743
|7,1=>0x7ce6f90df09bde37b66f60dea9bd2379e6f30de513c737886f04ddf1bbb37706ed4dd91baf37586ea4dd31ba337406e74dcd1b9737286e44dc71b8b37106e14dc11b7f36f86de4dbb1b7336e06db89b59b6836ca6d88daf9b5c36b26d58da99b50369a6d28da39b4436826cf8d9d9b38366a6cc8d979b2c3
|7,2=>0x7e66fc0df69bea3
|8,0=>0x10c8a18142e285850a8a14142628485088a10141e28385068a0c141628285048a08140e28185028a04140628085008a0013fe27f84fe89fc13f62
|9,0=>0x438186e30d861a8c341
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x11800021800042000083000104000204000400000670000c80000cc0001880003000004e000090000110000210000400000580000a0000120000220000400000580000800000e0000180000280000400000600000800000800000
|1=>0x11320022040044000084000106e0020c400418000823001040002044004040008010010000016180020800021000040e0006c4000c90001800002640004c0000900001120002220004400008200010200020000025000048800090
|2=>0x810c0102080202800401000800000e4dc018980029b70052ee00a0d0010100019b700300000405800808000e00001800002edc005cf800a000013ee0026fc004db8009b5001366002640004c0000936001260002444004800008b0
|3=>0x200000326dc0648980c90101912e0322480644180c1010180660300c40600980c0030153ee02a0dc045df808a9f011530022a38045448089b701122602227c044388069f700c0e201815c03008004a970093ee0126dc0244f804297
|4=>0x41b6e082edc105cb0209b7041224081040100800200820400200626dc0c0070149bf02913e0520640a04c81401f021b2c042edc085da810bb10215400426dc0844a010590020728040ac00815001029402052204040008018010005
|5=>0x9108e1127dc2241b84404608806e10a6dc214da8429b108526c10a2d0214120428150842681082c02104204203508406810801420cdb8419370832601026dc2045a0401040800000c36dc1864803059004736e08e0c01188b022010
|6=>0x200498a000042000043064d860c980c1920183220302000505c30a09b71413662826c4500c909099610426c2066d840c9b080fb7101f2c203e40407c0080f10101b6e202e40404db8800201000001221dc24438848851
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x200040004000202
|5,0=>0x400000100202600020d00000000000002000008302718040f0c320000000000270000000000020c0400
|6,0=>0x24a7a42365004c33051137780004233a00b104d64f345d81012500dd01d515007f000653cf00ac121425333e3d1a23991b3d9a006544110f010fa819003700db454f13010a105e231a10d60002670f0a0f2433a155bb25059023265040430f230082600112290b95c405190f4187bc1d104d0480260f00dc05b3350112ab3398
|6,1=>0x4c1d90fd919235b0135261a0f2229013c036e2c29a0310023145a043610bfc385740f6642517701281b4c5c210123264fae2697
|7,0=>0x49b8bad8b0d286b6497d0a49c877d09d8cbead9b49d7d0c9ba398449b3cb4b6921c707891ec2769f162356932b6dc06f478352704a5fb3d27b498b4972aa4913916c488fb78cdaa205c67e6b1c496a46102a61cd642d3807bd237073092fd1d11f463f7901b5177c7a62d43b0f92b77e03ca62b4884a590e57b2a4cea54e9d7e
|7,1=>0xaf7549a9
|8,0=>0xb948498ebacc717e49c56c9454688ea34a639658d3d38d47a6629e8ac7adaa
|9,0=>0x2eaa6c4b499c
|10,0=>0x49
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 8 roots_220 ops++addP pm 1 dom_212 7 roots_212 ops++addP pm 2 dom_202 7 roots_202 ops++addP pm 3 dom_204 5 roots_204 ops++addP pm 4 dom_158 8 roots_158 ops++addP pm 5 dom_218 8 roots_218 ops++addP pm 6 dom_216 5 roots_216 ops++addP pm 7 dom_206 8 roots_206 ops++addP pm 8 dom_214 8 roots_214 ops++addP pm 9 dom_142 5 roots_142 ops++addP pm 10 dom_198 5 roots_198 ops++addP pm 11 dom_94 8 roots_94 ops++addP pm 12 dom_210 5 roots_210 ops++addP pm 13 dom_90 5 roots_90 ops++addP pm 14 dom_92 5 roots_92 ops++addP pm 15 dom_156 5 roots_156 ops++addP pm 16 dom_78 5 roots_78 ops++addP pm 17 dom_86 5 roots_86 ops++addP pm 18 dom_154 5 roots_154 ops++addP pm 19 dom_150 5 roots_150 ops++addP pm 20 dom_200 4 roots_200 ops++addP pm 21 dom_196 4 roots_196 ops++addP pm 22 dom_194 4 roots_194 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_194 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 8 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 45 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 181 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 53 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 181 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 132 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 132 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 31 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_222 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_222 roots_222 goal_222 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_222
theorem lowS_222:Lower true dom_222 roots_222 goal_222 11:=S_222.noCircuit
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_234
def dzo_204_1:=0x2222000000000000222200000000000022220000000000002222
def gzo_204_1:=0x2222000000000000222000000000000022200000000000002200
def gsh_204_1:=0x1111000000000000111000000000000011100000000000001100
theorem lowS_zo_204_1_196:Lower true dzo_204_1 roots_204 gzo_204_1 5:=lower_iso_b (d1:=dom_204) (r1:=roots_204) (T1:=gsh_204_1) [(dom_204,1)] (by decide +kernel) (lower_slice_b (T:=gsh_204_1) [(0x1100000000000000110000000000000011000000000000001100,0,8)] (by decide +kernel) lowS_196)
def dzo_236_1:=0x222200002222000022220000222200002222000022220000222200002222
def gzo_236_1:=0x222200002222000022220000222000002222000022200000222200002200
def gsh_236_1:=0x111100001111000011110000111000001111000011100000111100001100
theorem lowS_zo_236_1_196:Lower true dzo_236_1 roots_236 gzo_236_1 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_1) [(dom_236,1)] (by decide +kernel) (lower_slice_b (T:=gsh_236_1) [(0x110000001100000011000000110000001100000011000000110000001100,0,8),(0x111100000000000011110000000000001111000000000000111100000000,0,32)] (by decide +kernel) lowS_196)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,36),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,40),(32,96),(32,160),(64,68),(64,72),(64,96),(64,192),(65,69),(65,73),(65,97),(65,193),(128,132),(128,136),(128,160),(128,192),(129,133),(129,137),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x753ea73bb0
|6,0=>0xf678bd2c887ebc37941670ce63db102c33125d04
|7,0=>0xc9d719cbe891bd5399973035d2a54f21aa22030e014cf
|8,0=>0xbad389f23b43d29
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000cccc0000cccc00000003333000033330000333300003333000022220000222200002222000022220000000000000000cccc0000cccc0000000000000000000088880000888b3330000333300003333000033330000333300003333000033330000000088880000888800008888000088880000888800008888000088880000888b33300003333000033330000333300003333000033330000000000000000cccc0000cccc00000000000000000000cccc0000cccc000000000000000333300003333000033330000333300003333000000000000333300000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c333300003333000033330000333300003333000033330000222200002222cccc0000cccc0000cccc000000000000cccc0000cccc0000cccc0000000333300000000000033330000000000003333000000000000333300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc03333000033330000222200002222000033330000333300002222000022220c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0000000333300003333000033330000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x37b905837b90c437b905437204376905437e90437d90f437b90c5437b908437ba95837ba43b190c43b1905837e98437d9c543720543760843b19058376543210
|1=>0x437b90437ba9043729084
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863262b72561f61871260b7
|7,0=>0x7476d76766165a75464d74583e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x241b95014950189501b9525ba641b0525e9ec150d255052590501496414071f8950189501496c1407a7b0501506e5496e909525c7e25406e909525
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd43488f330c9318c42
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x36e7a62cb9d7de2e6dfa5b9a5ccbfe5fb2bd95e8aee37313007f82e615101f0080004000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x60
|6,0=>0x4105051cc1
|7,0=>0x13ac9ac5c68f
|8,0=>0x212e
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 8 roots_236 ops++addP pm 1 dom_205 7 roots_205 ops++addP pm 2 dom_172 5 roots_172 ops++addP pm 3 dom_108 5 roots_108 ops++addP pm 4 dom_229 8 roots_229 ops++addP pm 5 dom_233 8 roots_233 ops++addP pm 6 dom_109 7 roots_109 ops++addP pm 7 dzo_204_1 5 roots_204 ops++addP pm 8 dom_173 7 roots_173 ops++addP pm 9 dom_45 5 roots_45 ops++addP pm 10 dzo_236_1 6 roots_236 ops++addP pm 11 dom_77 4 roots_77 ops++addP pm 12 dom_141 4 roots_141 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_204_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_236_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_141 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 8 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_238
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(4,36),(4,68),(4,132),(6,14),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,44),(12,76),(12,140),(32,34),(32,36),(32,40),(32,96),(32,160),(64,66),(64,68),(64,72),(64,96),(64,192),(128,130),(128,132),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_238.map (·&&&dom_238)
def gM:=goal_238&&&dom_238
def NN:Nat→Nat
|4=>4
|5=>70
|6=>153
|7=>94
|8=>23
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x8d1ae48e25478cc21319
|5,0=>0xbbbffb99f3a493b8e96c7b3c971d83638a46239d5f7665e5b05e28e5c6805acc059ce2599175547e552365193f4bfad4ab41481f245885442bd4398941f9a4161f4045b3fe033e30c39c8139c7838f5f37ded36f30342cf335bc2b15829c6028f3328a45210741eff01eeb31e9631e79a1d5ad1d58f1c4381beef16e83165f21322b12dd5126f5100e80f0de0ee360c78e0b8210aaf40a6a00930e0837907c2e07a6905c60038250311102fb502a7d
|6,0=>0x58a7955c0154a7251a5a507544fff64f7ed4f45c4d0944c3264c2b74af7a4ae1e4a0c1496c047fe247f9546a39449aa449934411843ed942d9541f1f4015c3fe033fcb33bf3e39ee0398f238fa63876c3842b361f435fa234df13378032dfd32def3278f3205431b0e30b24304f6303a22fb882eb892d31d2bfd02b1732aec229a3228a73287872714d25adb25784256ee243db21192206f02038c1f8851ec151ea761dd351daec1ce0a1b1cf1a9861a9671a52c19fb2190541843716dc316d40168911667b14fae1470f1405a13f991383b137f712bf012b6e12a1311ab911a1c1185d10bcf1057110565103ff0ff350ee120ed3a0e4c70d8e20d1bf0cb9f0c2ce0b50a0b0c00aea30a3c1099490988b0930e08d7d08cc608812084e3065620629e06252050270471e03dd503ceb035a40322d03011027600193600e7100aba
|6,1=>0xdfd9c8d6ee815fa79104745ae72c376f41c6d9ba698e4693da6790a6733b64f8e621e061fb05f7665f6695ec935df355d4ba5c8de5c6aa5b19d5a8fc5a584
|7,0=>0xe94a1a74d39294c922b9826d37d3f57a860751866f5e56eabc696ce6903d64c7363b4860b9c5de735ccf25b389570095439f530a751d1b50f5b5032e4f67a4e2d44c39a4b40d4a68e4554a4544844fdb421763fdc03face3eb533d6993c4f43a19b3a0d2383ca3588932a0e320cb3112930e2c2fa2d2eb682e1852d9202ad672a7f9286852785b26c2f2610825ee424eca24c5d24c512388b21b75216e820ae81facb1f0b21d8521d0361ba691abfe19b7a17c271662112d3012a13103471021f0f9570ede60dba90d7d40d0550bfb90bda80b67009ffb07e24075bd0577d042460315f02a8201fc4018ff
|8,0=>0xe9ae9a5d407a39478f376a16b5a52a5005e429cc404533c2a234be23356d27008221951e0761c1e717020135ca122911006a0ffab0ff9f06354
|9,0=>0x68b393cb3c3543809a8c
|10,0=>0x1305b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa8a80000a8a80000a8a80000a8a80000a8a80000a8a80000a8a80000a8a8000000015554000000000001555400000000000155540000000000011112aaa80002aaa80002aaa8000000000002aaa80002aaa80002aaa80000000555500005555000055550000555500004444000044440000444400004444aaaa0000aaaa00008888000088880000aaaa000000000000888800000001540000015400000154000001540000015400000154000001540000015402aaa80002aaa80002aaa80002aaa80002aaa8000000000002aaa80000000555500005555000044440000444400005555000055550000444400004444aaaa000000000000aaaa000000000000aaaa000000000000aaaa00000001111000011110000111100001111000011110000111100001111000011112aaa80002aaa80002aaa80002aaa80000000000000000000000000000000555500005555000000000000000000005555000055550000000000000000aaaa000088880000aaaa000088880000aaaa000088880000aaaa0000888955540001555400015510000155100001555400015400000155100001540282800002828000028280000282800002828000028280000282800002828555500005555000055550000555500005555000055550000000000000000
|0,1=>0xaaaa000088880000aaaa000088880000aaaa00008888000000000000000155540001515000015554000151500001555400015150000141400001414008080000080800000808000008080000080800000808000008080000000005500000055000000550000005500000055000000550000005500000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000088880000aaaa0000888800000000000000015554000155540000000000000000000155540001111028280000282800002828000028280000282800002828000028280000000555500005555000055550000555500005555000055550000555500004444aaaa0000aaaa0000aaaa000088880000aaaa0000aaaa0000aaaa0000888801540000015400000154000001540000015400000154000001540000011000000000000000000000000000000002aaa80002aaa80002aaa80002a805555000055550000555500005555000055550000555500005555000000000000000000000000aaaa0000aaaa00000000000000000000aaaa0000aa0155400001554000015540000155400001554000015540000155400001554000000002aaa8000000000002aaa8000000000002aaa8000000000002a80000000000000000000000000000000005555000055550000555500004444
|0,2=>0xaaaa0000aaa00000aaaa0000aaa00000aaaa0000aaa00000a0a00000a0a1555400015554000154000001540000015554000155540001540000015402aaa80002aaa80002aaa80002aaa80002aaa80002a8000002aaa80002a805555000055550000555500005555000000000000555500000000000055008a8a00008a8a00008a8a00008a8a00008a8a00008a8a00008a8a0000888954140001541400015414000154140001541400015414000154140001540088080000880800008808000088080000880800008808000088080000880555500005555000055550000555500005500000055000000550000005500222200002222000022220000222200002222000022220000222200002201555400000000000155540001555400015554000000000001555400015402aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002a80555500005555000055550000550000005555000055550000555500005500aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa000000aa0155540001540000015554000154000001555400015400000155540001540000280000002800000028000000280000002800000028000000280000000050500000505000005050000050500000505000005050000050500000500
|0,3=>0xaaaa0000aa0044440000444400004444000044440000444400004444000044440000000000000000888800000000000088880000000000008888000000000000000555500001111000055550000111100005555000011110000555500000000aaaa0000aaaa0000aa000000aa000000aaaa000000000000aa000000000155540001555400015510000155100001555400011110000155100001111028280000282800002828000028280000282800002828000028280000202555500005555000055550000000000004444000044440000444400000000aaaa0000aaaa0000aaaa0000aa000000aa880000aa880000aa880000aa0001140000011400000114000001140000011400000114000001140000011008080000080800000808000008080000080800000808000008080000080555500005544000055550000554400005555000055440000550000005500aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000888800008888000000000154000000000000015400000000000001540000000000000002aaa8000002a80002aaa8000002a80002aaa8000002a80002aaa80000000555500005500000055550000550000005555000055000000000000000000
|0,4=>0xaaaa0000aaaa00000000000000000000aaaa0000aaaa0000aaaa0000aa0000000001555400000000000155540000000000015554000000000000000000000000000000000000000000000002aaa8000222200002aaa800022220000000000000000000000000000000000000000555500000000000055000000000000000000222200002222000000000000000000002222000000015554000155540001555400000000000154000001540000015400000000000000000000000002aaa80002a80000000000000000000002aaa80002a800000000055550000000000005555000000000000550000000000000055000000000000000000aaaa0000888800000000000000000000aaaa00008888000000000000000000000000000000000154000001540000015400000002aaa80002aaa80002aaa80002aaa8000002a8000002a8000002a80000000000000000000000000000000000000000000000055550000000000004444aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa000000000000888955540001555400015554000155540000444400004444000044440000000088880000888800008888000000000000888800008888000088880000000050500000505000005050000050500000101000001010000010100000000
|0,5=>0xaa000000aa0000000000000000000000aa0000000154000001540000015554000155540001540000015400000155540001540000000000000000000000000000000002aaa80002aaa8000222200002222005500000055000000550000005500000055000000550000000000000000aaaa0000aaaa0000aaaa0000aaaa00000000000000000000aaaa0000aa00000000000000000000000000000000015554000155540001555400000000000000000000000000000002aaa80000000000000000000000000002222111100001111000011110000111100001111000000000000111100000000aaaa0000aaaa00002222000022220000aaaa0000aaaa00002222000000001414000014140000040400000404000014140000141400000404000000000000000000000002aaa80002aaa800000000000000000002aaa80000000444400004444000055550000555500004444000044440000555500004444000000000000000000000000aaaa0000000000000000000000000000aa00000000015554000000000001555400000000000111100000000000011112aaa80002aaa8000000000002aaa80002aaa80002aaa8000000000002222000000000000000000000000000000005555000055000000555500005500
|0,6=>0x2aaa80002aaa80002a8000002a800055000000550000005500000000000000550000005500000055000000000000000000000000aaaa0000aaaa0000000000000000000088880000888955540000000000015554000155540001555400000000000155540001111088880000888800008888000088880000888800008888000000000000000000000000000000000000000000000000000000000000000555500004444
|_,_=>0
def sP:Nat→Nat
|0=>0x521028714ace840a2438a521028724a13840a986920c102a5261c9060a54689241820d12491860088a0642102940e2861d081c506401028914783042e1c51d0814a870218e04366868a1e1438a1030c80304038a1e10b871e582052a503920c109920c44290143c7041a0808c0608080
|1=>0xa68a07143c2930e483000a3449246a0307149da840a1da0110151120c44205482492e0c00807143c0042ab43920c10d8d143d9855a4c3920c0038a10742052e2878e08152870c84205063451d0815131241820512297860888a2e0c642ad0e190840a243920cb021a1a1c50f0a1d50a
|2=>0xe280be08943920c102ad1a483000e295be081448a0221c07040460444ec086000db8108141bc143c2052a1c92e0c00689143d9900e2878c0835d0a02143ae0c840052e3448a1e003867258205343448a1e144b70218217062450f004c5010c442870218b040a9049246182090e19b04
|3=>0xe287840ab438a0c802050e2978608148030e2808c080ca0d14046044434086381029712287840a886a35c0430526243920c102940e2878c0010d87140440c001c506801028914046061c1038a52642054a1c927081438a5210295261c5010c5038a52102870c64b040a3450f1038290
|4=>0x22102980e287b30816389143c2050ea05010d14203140598e08152150e2808600906891404300121c5010d0c2071420319001418a02187040a243aa141820506245017c102940e28321081438a0c802052a1c5010c002250e28320081418a022c2052a1d70a021800312280b30010b9b
|5=>0x814a070218b040a503ae50043100e287840a1c50f112c205122808682011145c043000a6c68a02202891404311001120724b83000a9468724182054a1c5010c10289152808608503ae0218e055a345010c0248950043040eb808690016875c04300065050f0814d87143c004448c086
|6=>0x814392501824e48343a8021800d0e280a708146895ca00861a1c92350182890e4918600108140e28086093468a0220287241a6040a6c18d143c205281d70a0c642a414043110814a0714ac3040a344a35c28086301c50f181029b341c50f081418a02307040a5c38a1ecc2054824906
|7=>0x400020528280861c102ad26345010c16a07143c205445050632102c912483040a6038a02f82051a1c906a6102a2128d7010c10b8d0e287800a88a280218207140440c9c5068724a03040edc086081522d0e280860040689140430444511810c10287143e8840ab469250182059e1c906
|8=>0x1418c840a1c50110e028714ac3040a603810c582055a1c50632102940eb94010c003810c582051a2492e0c14c090e287840a0ca0a1e002050e2840672102ad1a8c5010c156870218e040a5c38a02f82054a503920c102940e497060a6838a1e302055a503920c1028714190840a1c506
|9=>0xa1c53b021800d1228086b96c38a02180040768501101468a02198052e1c5063210287140443e08143ae02198051a1c50fb2102a4261c5010c1438a0d5eb040a6080714043042e1c0862c102871418ca108143d5143c6040e48311001028d12287880a50487143c60436345010c01287
|10=>0x1418e21081438a56180040a1c0862c00205065068a02202ad1aa05010c016a21a28086001c5063a002050e044062c10283122808800943920c1029b1a280881814c0a02187040a1dd0a02102d40e28088081438a0c840040a9568724182050e295863210287248c31108141941405984
|11=>0x61c5010c10287143d9840a0ca0d14043040a5038a1e180040a343ae500430544257010c102cd0e287840a0c48a0218004921c9060814687140431c081468746b85010c14d8d14046060814a0714190040a5c68914043000e28319381028d1228786001c9280c44205281c9230c10287
|12=>0xa3438a0219f040a1c5010c11e850eb85010d7c205281c506321028d0e287880a6ca0714043040afc38a0218205441d1ae0218205281d70a02180054a1c5010c102830e280b318102901a1c5010c102a55a1c5010c102890e49406081d18a02188840b7838a02182051a1c501ba18290
|13=>0x81438a1ecc4040a243a35c2808608503a814043041a245011818222282808600102875028086221029b0e280880814a07140431c0814a07462808608170071404300081438a021a40008b438a0218004363448a0218205b41c5011018287248d7060814a07140460608911091404304
|14=>0x5a4c38a02182050e28319081418d14046040b6c38a0218205301c5010c00205121c5010d302051a1c5010d702a50e280860010287140434b081710714043040a6038a02203040a1c50f66002050e280880d382890e280880c0268714044040a6838a02182050e28086a6102bc0e28086
|15=>0x1a28086081438a02182300a3438a1e18005441f2810c102ad0e483040a2438a1e2020528243ae14043051a2490a0c102890e49706081438a021b2000a1ea8a1e18205061c501ba10287140431c0814a090e28786081568746280860814b8914043040a503921418205281c5063200205
|16=>0x1028d0e2808c0c102871404304b81438a021a4040ab438a0218205121d70a02182054a5038a02182052a3438a02182050634501101520d0ea008608146891404300483448a02182050e28086087c2971a1c5010c002a2aa28086081438a0c640040a1d728021801b121c50f0814d83
|17=>0x814a0714043040a0c38a0220205061c50f08143a31404300081468714043000a1ea8a0218205483438a02182050e2808818102970e280880c102875c28086001418d14043040a1c50f0c002051a1c90a0c102a40eb85010c102970e2808608143e514043040a1c50f18102940e28086
|18=>0x1c5010c102a20e28086081438a02180040a1c50110182050e28786
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xd5008500440004
|5,0=>0x181617b61756170516a61655160515b51565150614a6145513f613a5134612e61286122611d51176111610b610560ff60f960f360ed60e760e250dc60d660d060ca60c460be60b860b260ac60a660a0609b5095608f60896083607d60776071606b6065605f60596053604d60476041603c50366030602a6024601e601860126
|5,1=>0x1a4619e61995193618d61876
|6,0=>0x34f73496343633c7335732e7327732073197312730b730472fe62f772f162eb62e472de62d772d162ca72c372bc72b572af62a872a2629c62966290628a6284627d7276727062697262725b7254724d7246723f72387231722a7224621d721672106209720271fb71f471ee61e771e071d971d361cc71c571be71b771b161aa7
|6,1=>0x4f964f364ec74e664e064d974d274cc64c574be74b774b074a974a2749c6495748f64887482647b7475646f64687461745a7454644e6447744074397432742b7424741d741764107409740363fc73f573ee73e863e173db63d473cd73c673bf73b963b363ac73a6639f73987391738b6384737e63786371736a7364635d73567
|6,2=>0x5a3759c7595758f65887581757a7573756c7565755e7557755075497543653d6536752f75296522751b7514750d750674ff7
|7,0=>0x7788772676b7764775c8754874d7745873e7737772f87287721771a7713770c770576fe76f776ef86e876e176d986d186ca76c286ba86b286ab76a4769c8695768e7687767f8677867076688661765b6653864c7644863c8635762d8625861d8617660f8608760175f985f365eb85e385dc75d575cf65c875c265ba85b285aa8
|7,1=>0x85088488842683a8834682c8825781d8816780f7809680277fa87f377ec77e577df67d877d087c977c277bb77b477ad77a6779e8796878f778877808
|8,0=>0x8f778f078ea68e288db78d478cc88c578bd88b678af78a878a178998892788b7885687d8875886e7867786078588
|9,0=>0x912790b790478fe6
|10,0=>0x9196
|_,_=>0
def wAt:=mkWire dB 102 239 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe195c1d08290a1d02290c051811181d0a195a134a4b12b908290e15641d008b0815600500880815141d0a1d28070e010a1128070e010815541b146528070825481714010e1502290e110a110e010815001d0815027d0e15000c0e190815361328070e0108150c150c15162912200a1d0c110e1116290e1912200e150c110a11
|1=>0x22918340e110a1d0c1508190c15142d122008190e150e2912b80e1514110a110e1914e11a300a190e117a1d000f081502190c010e150e110a11761912b80a1d14110e110e151a1902190a1136130e1514e11a300a190e110a11021906110c1d14050eb95c15082914ae0c6528070825501114150229081d147d000c08150c11
|2=>0x81948175c1d1411001908150c1d080d0a0d0c1d021902c100880e2908150a5e080d0c1d1a150e110a19282b0a35081d0c3502190a1d081d0e290ab914110e115a1312290e1502290c050c150e01081508150e310c150c1184070b050c36081d0ece08310c154a1b12b908290e1502297e01008a0e2908150a114415081d141d
|3=>0x12190e150219461f14010a110ecd18110c1502190e1506130c1d02198c151aa30a29081d661f08310c1548171435081d14350a1d0a110e118815122208190e150c1128070e010a11301f000d0e190a11146528070825281b08250e1528070e0108154a0748151435081d4a17461d140108154a0748151435081d12200e150c1d
|4=>0xe0108151a150e11141114152e171a190e1102190c360a1d0a110e11001d0a11141d181d081d0c110a19461f140108155c1d0a11141102291aa10a290e1102297e01008a0e2908150a1d1aa00a29081d282b001d0a1114250815081d0a1d44131415141d0a1d0ea208151415141108150ea114151411001d0e19081502190815
|5=>0x481514350e150e111411141550110a290e110229140102290e1508151a150a5e0c35081d06170c1d0c110e1112ba08290e15022902190e1106150c1d28070e010a110eb9461f0ab914110c6528070e0108150e150ab914111a310a190e110c0536130c250a1d661f08310c150e2110150c11021944110a1d141d0229302b2819
|6=>0xa1d141d0229301b2e150c35081d1aa20a2902295c150e1508291a1902190e110a111a150e11141d0a290c150e020c110a111a150a290e11022914e11a300a19081d088944150e2908152e170c350e110e2914010e01081502190949181f0c150ea10a290e110229a0114417141d0229001f08151415022914151435081d4a1b
|7=>0xe1108290e150229086d0c250e1502190e1902190e010815300712210a1d5011501d0a290e11282b142508250e151a19281b0a35081d28291a150e111a150e111411022902193613181d0c151405142508250e15284b1a150e1102294a07461d14010ece0c010e0108155a134415141d0c05aa1908260e1528070e0108154413
|8=>0xa1d141100880e290a1102191a320a1944115a134415141d09610c260e152e152e170c35081d28070e0108150c15021908260e150e8e1401081502290c1102190a1d081d12110e150c1502190c250815081d0a1d28070e0108151a300e110c110c1528070e010815302b2e150c35081d0e01081514151411302b2e150c35081d
|9=>0xe150c1d081912b908290e150229181d0a190e11301f2e150c35081d0ced12b808290e150d2d122308190a1d146628070e0108155a1112290e15022928070e0108151405461f140108150c1d001d0c010a1112b80e1514110a110e1514020e110a110afd008a0e290a110c110e190a360e110e1100880e290a11301b12210819
|10=>0xa110c1d0a1d1405088a141d282b0a35081d0ab914110e11181d0a190e1128290e0108150c350a1d0a110e11282b0e0108150e1502190e110a111405461f08a114150e01140108150229282b0e0108150c6528070e01302b000d0e191a150c110c1d081d0ea10e11141508154415141d02fa281b0e010815302b12210a1d0a11
|11=>0xa1d28070e0108150e110c11021912110c250a1d008a0e290815141d0ab9141114110e010a1148151435081d08310c150c1d2e170c35081d5a1114250a1d0e1514150229461f14010815aa2908260e1510170c110e112e1706110c1d18110c1502191a150c1d081d02190e0108150e11141114151411141d0a1d06170c1d0219
|12=>0xa1d1aa20a29081d0f850c0208150a210c1102195c1508290e150a290a35081d0e150a190e110e290e010815461f08a114150e310c150c11282b0e01081514010e010815000e0e190ea2141508150ea1141508150e110c250a1d0c110a360e115c1514110229001d0c1508154411141d0a1d281b0a35081d000f0e19081512bb
|13=>0x282b0e01081512110e1502195011501d141506110c1d0a1d1a150e11022928070e0108155a1314250a1d28070e0108150e110c1d0a199215088a141d000d0e19081512ba082914020e110a11461d14010815122308190e150f8d18130c15122108190a1d0c01081502190e020c110a110e150c110a110a0e0c1d0c1136130c25
|14=>0x81d14151435081d0e150e110a1114350a1d081d000c0e19081508150c35081d0e2908260e1528070e01081508151415141112190e1502190e1106150c1d00880e29081502190e110a11141d0aba141112290e15022908190e150219121108290a1d0e15081d02290e15141102291a2b0e110a11021908260e150e1910170c11
|15=>0xe2908150c1102190e0108150c110e190c050e19140108150e110a1108260e151435081d0c150c11101d0c1114110a110c1d081d081502190e1102290eb914110c35081d5c1714110c1502190e0108150a19081d140208150ea2141514250e1508290e1528290e0108150a921435081d0c110c1d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x198006
|5,0=>0x21107f500007a51d547051ad4683000063500005e500005a40000591151450400000001310484000000011100000fd40000ed000000003740d84000000032400002f30a9427300000000000000090c204000000000001f1069418205880000454000000010103100000000000
|5,1=>0x88500000000000000
|6,0=>0x5b916a4599162457cd5b455d1543544d4d4528d46450913e44e9136400013244bcd2b44a0d24448111c4461115344510d442510544050fd43e8cf643c90ee43acce833910e043710d84354cd2333cccb431d0c342fd0bc32e4cb540000b142b8cab32a0ca4428109c4261094424108d3
|6,1=>0x94d24f492d247490d00008fd23b48e0e3448c4e2d400022a3899222487921a4859213383d20c3821000081120047f11f847d11f137b51e947951e237791da47591d2473cdcb4720dc44704dbd46e51b636ccdaf46ad1a7468d19f466d19836511904631188461118135f8d7a45d91724
|6,2=>0x2ae3aa92a73a8d29f4a6d2983a54e923a3928b3a20e844a04e7d49e527639c926e49a9266498925f396d2574
|7,0=>0xdacf683d94f623d7cf5d2d68f573d50f513d38f4b3d20f453d08f3f3cf0f393cd8f333cc0f2d3ca8f273c90f213c78f1c2c64f163c4cf103c34f0a3c1cf043c04eff2bf0ef93bd8ef33bc0eed3ba8ee73b90ee13b78edb3b60ed53b48ecf3b30ec93b18ec33b00ebd3ae8eb73ad0eb13
|7,1=>0xf14fc23efcfbc3ee4fb63eccfb03eb4faa3e9cfa43e84f9e3e6cf983e54f923e3cf8c3e24f863e0cf803df4f7a3ddcf743dc4f6e3
|8,0=>0x3f42fc8bf02fb8bec2fa8be82f98be42f88be02f78bdc2f68bd82f58bd42f48bd02f38bcc2f28bc82
|9,0=>0xfe47f81fdc7f61
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0xd080060000208000ec0006780032400190000c300060000284001200008400040800200000f200068000308001300009000044000208001000005200021000100000500001e000090000400000c0000200000
|1=>0x1060008184040080200000c6280610402fda016ed00af68053b4027da012ed008f68043f4021da010ec0087280438002182010c0008300041000204001004008008040000108a007a0003760013b00080000380
|2=>0x880004179020028100040687e8243b4101b0080d00405082024010100080000287e8143f0081100404802014810080080100400001a7680c910063da031e5018e200c3b404dc8025e401272008b0004480021c0
|3=>0x140300a01004a1da250e41207a090390421da200fd1006e080270400c2200000c07e8603b43017a150ed0a07a04cb94263da131e5098e204c69426308130ed090f284861022bda112ed0897084479422388110a1
|4=>0x520702803b5400da940ac48a76a443b520010890fd4406a220341101388809841872a0839502fda814ed4087ea043b500788802804007ea003610012080080200428c43f4601da300dc1804e0c01705a1ca280c8
|5=>0xc0220600236521db280ed94074ca038650191280699007ec803b640081180318a876c45192225cb11000882604403b61a1db0804081b76c0cb96065810326181922408996029db010fd80876c0408600bc100008
|6=>0x1950edc8a606443b7221cb910cdc8842e44117201db900c9c8064640307201539008dc8034e4002708109830e5c1090e047970210b80480
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x202
|5,0=>0x27000000000000087f006018112521002400050040003c3a3d000014120000550087000600001754000008004c100300000000071200000074584c21002b00003c2a000000
|6,0=>0x8b9d0b6785002778120101010003a1595ebfa84e62290400cc276f1faf261901014f9c3f51300a01b536037a08125666c792c53b0e3d19237e7c9f5d12b45696016a524a0301278908421e147b01c922006399a655765708ae99b8bb71bab24556164304205d84132827125f4d090b08485c8c0c001c1db0a0449580c0a92e88
|6,1=>0x16b01361550010a0acfacb52a26c32f41011b270d0f29562c
|7,0=>0x9776d83d2824669b6d098aba7799b788137cbb35372a54831d3196cd4cab9316e793e129e75a334a29193c248315a8e3995cdb1cb8aaac61a0a72bca7625bd182c18e03d0652d7997c8318d470fad94a3626139ced373b74bc47dbe95a9
|8,0=>0xd2494b989aa386356d8f689070866d3238d0648e5abda4
|9,0=>0x798e3336
|10,0=>0x31
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 21 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 9 roots_234 ops++addP pm 1 dom_164 4 roots_164 ops++addP pm 2 dom_110 8 roots_110 ops++addP pm 3 dom_230 8 roots_230 ops++addP pm 4 dom_166 5 roots_166 ops++addP pm 5 dom_228 7 roots_228 ops++addP pm 6 dom_174 8 roots_174 ops++addP pm 7 dom_206 8 roots_206 ops++addP pm 8 dom_172 5 roots_172 ops++addP pm 9 dom_108 5 roots_108 ops++addP pm 10 dom_232 7 roots_232 ops++addP pm 11 dom_100 4 roots_100 ops++addP pm 12 dom_236 8 roots_236 ops++addP pm 13 dom_204 5 roots_204 ops++addP pm 14 dom_226 7 roots_226 ops++addP pm 15 dom_102 5 roots_102 ops++addP pm 16 dom_142 5 roots_142 ops++addP pm 17 dom_198 5 roots_198 ops++addP pm 18 dom_196 4 roots_196 ops++addP pm 19 dom_46 5 roots_46 ops++addP pm 20 dom_78 5 roots_78 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_238 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_78 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 9 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_238 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_238==dom_238)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_238 gM v ys):RunD true dom_238 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_238 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 70 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 153 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 25 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 153 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 94 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 94 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 23 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 23 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_238 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_238 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_238 roots_238 goal_238 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_238
theorem lowS_238:Lower true dom_238 roots_238 goal_238 11:=S_238.noCircuit
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_slice_b [(0x22002200220022002200220022002200220022002200220022002200220022,16,17)] (by decide +kernel) lowS_244
namespace S_246
def pG:List (Nat×Nat):=[(2,34),(2,66),(2,130),(4,20),(4,36),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,20),(16,80),(16,144),(18,22),(18,50),(18,82),(18,146),(32,34),(32,36),(32,96),(32,160),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(64,192),(128,130),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xc602d
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x154015400000000015401540000000001540154000000000154015400000002a8000002a8000002a8000002a8000002a8000002a8000002a8000002a8000500050005000500050005000500050005000500050005000500050005000508800880088008800880088008800880088008800880088008800880088008954015401540154015401540154015401540154015401540000000000000002a802a802a802a8000000000000000002a802a802a802a800000000000000055005500550055005500550055005500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_244 8 roots_244 ops++addP pm 1 dom_182 7 roots_182 ops++addP pm 2 dom_118 7 roots_118 ops++addP pm 3 dom_242 8 roots_242 ops++addP pm 4 dom_230 8 roots_230 ops++addP pm 5 dom_214 8 roots_214 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_214 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 8 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=S_246.noCircuit
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x202020202020202020202020202020202020202020202020202020202020202,8,9)] (by decide +kernel) lowS_248
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_119
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 10:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_123
def isoMvS_221:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_123
def isoMvS_243:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_123
def isoMvS_250:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_235
def isoMvS_252:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_246
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_126
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_222
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_238
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
def dzo_210_1:=0xa000a00000000000a000a00000000000a000a00000000000a000a
def gzo_210_1:=0xa000a00000000000a000800000000000a000800000000000a0000
def gsh_210_1:=0x50005000000000005000400000000000500040000000000050000
theorem lowS_zo_210_1_194:Lower true dzo_210_1 roots_210 gzo_210_1 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_1) [(dom_210,1)] (by decide +kernel) (lower_slice_b (T:=gsh_210_1) [(0x50000000000000005000000000000000500000000000000050000,0,16)] (by decide +kernel) lowS_194)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_42:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_242_1:=0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a
def gzo_242_1:=0xa000a000a000a000a000a000a0008000a000a000a0008000a000a000a0000
def gsh_242_1:=0x5000500050005000500050005000400050005000500040005000500050000
theorem lowS_zo_242_1_194:Lower true dzo_242_1 roots_242 gzo_242_1 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_1) [(dom_242,1)] (by decide +kernel) (lower_slice_b (T:=gsh_242_1) [(0x5000000050000000500000005000000050000000500000005000000050000,0,16),(0x5000500000000000500050000000000050005000000000005000500000000,0,32)] (by decide +kernel) lowS_194)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000505000000000000000000000504000004000000
def gsh_170_16:=0x5050000050500000000000000000000050400000400
theorem lowS_zo_170_16_42:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x5050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a0a0a0a0a0a0a080a0a0a0a0a0a0a00
def gsh_250_1:=0x505050505050505050505050505050405050505050505040505050505050500
theorem lowS_zo_250_1_194:Lower true dzo_250_1 roots_250 gzo_250_1 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_1) [(dom_250,1)] (by decide +kernel) (lower_slice_b (T:=gsh_250_1) [(0x500050005000500050005000500050005000500050005000500050005000500,0,8),(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050500000000050505050000000005050505000000000505050500000000,0,32)] (by decide +kernel) lowS_194)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050500000504000004000000
def gsh_234_16:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_16_42:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_218_1:=0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a
def gzo_218_1:=0xa0a0a0a000000000a0a0a08000000000a0a0a08000000000a0a0a00
def gsh_218_1:=0x5050505000000000505050400000000050505040000000005050500
theorem lowS_zo_218_1_194:Lower true dzo_218_1 roots_218 gzo_218_1 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_1) [(dom_218,1)] (by decide +kernel) (lower_slice_b (T:=gsh_218_1) [(0x5000500000000000500050000000000050005000000000005000500,0,8),(0x5050000000000000505000000000000050500000000000005050000,0,16)] (by decide +kernel) lowS_194)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_16_42:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_234_1:=0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a
def gzo_234_1:=0xa0a00000a0a00000a0a00000a0800000a0a00000a0800000a0a00000a00
def gsh_234_1:=0x50500000505000005050000050400000505000005040000050500000500
theorem lowS_zo_234_1_194:Lower true dzo_234_1 roots_234 gzo_234_1 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_1) [(dom_234,1)] (by decide +kernel) (lower_slice_b (T:=gsh_234_1) [(0x50000000500000005000000050000000500000005000000050000000500,0,8),(0x50500000000000005050000000000000505000000000000050500000000,0,32)] (by decide +kernel) lowS_194)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(16,17),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,96),(64,192),(65,67),(65,73),(65,81),(65,97),(65,193),(128,130),(128,136),(128,144),(128,160),(128,192),(129,131),(129,137),(129,145),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
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
|4,0=>0xe587faa0e63580e21c29
|5,0=>0xe587fbb8daacba49314887875791ca638a661b0d6135b59f6b574c553d1b525b84f2f149835431b94109e40bb53c6943ab163aa8f39a963820337dc13786a3580e3497f32dd52de082a7082814827f2326d7525c5b259312534e24e8d21d3e213a51f3b01dcb31c0b415a261353b1172e114290f8540d8830cbaf0c7930c37e0ba530b5410b1da0a90d0a09b09f64088670820507da3071bf067db0535f04bbd04224036de02e9c01a0d00d8b
|6,0=>0x1fae11fabd1ee9f1e2b81dfd01c7191a7cc196b718cea180a517fb717c1f179c3173df1724e16b53164e01618d15a051524a14d6a14cda14b3e1488113b4213a4313883135d9130a71308f12d4312bec127491271b11f18117da114281110810a56108c31068e1062a100c8100bc100b20ff8e0fd120fc5d0f7090f2ab0e6ea0e4010e1cb0d0720cf8c0ca0a0c8ca0c0900bec90bd920bcf50bb8d0ba3c0b8db0b6f70b1fd0adfe0abff0a7430a4de09df309d8e09ba409981093f50929808d19083bf07e7507cf707c6b07946078bd0773d0734f072f906da406a6f0665e06427061b205e4e05daa0537f04efc04ef604e7e04ca004aee044510430704267042130406903ca403bcf0394e037620373503702036240330d02d6802b4f0297b0252101efe01a9f0182b0158a011c800c6900bbb00a0f002c30017d000a9000a7
|6,1=>0xc534fb273eacba48fd018dabd8b84a814317ad9376cab76541757a973b26717156b5626a7d76643663f8a62c9c5cdc0574c55649c549ac541cd51ad54f5ea4e7dc4d3f44b2c14901747d6e4742f4574c44d3743b25437f34341840a54403193e96d3dc683dbbf3d9613d1883cecd3cbd33c7593c0bd3b58e3b2ce3a9b23a4183a2803a0ad39fd538857386ea37e6b376aa35ba935ae13573134a1d344e732e7a323cc321be31e3f31e0d3105f3078a2eb052eaad2e8a32e2e22c9b22c93f2c8892c2c02b9ad2ad462a8e528e3228b51288c9284922800c2701626b1d265862637e25fca25d0b25c4325bf82517824f762471f23ade238e1231ba2305e22f35220a4215c1210bf20f9620015
|7,0=>0x134fb1334f1322c12c0c1276111bf911b1a11a67117f8117521104810d971079d10617102e4101c0100780f8780f6710f4a60f2220ef430ee840edef0eb7b0e4ff0e3940de670d8470d36d0d2cc0d2680d02b0cc040cbee0c8510c5270c07d0bc9c0bc5b0bab30b98b0b6bb0b49d0b08c0afef0ab9f0aa7c0a9d80a98e0a7100a5d00a56b0a5630a20a09e7d09be109a8a094e8092e0091be08d4208b5a0854308306081b707d7907cf40779106f7506f4d0693c0668c063b706348062d705f3405e9705c8305a8105530052b8052ae05257051860503e04f8d04ee404ee304ed504e6d04d9904a9c048ba0457c044ad0420f041d903d6603d3803d05039ea035e1035910351e034b102f7702db302a9702a8e029f3025a6020e6020c801ed701c86018b4017cd0173d0161a015a50144000c3400b4400b370054f003c600136
|7,1=>0x4d29c4d18e4cfac4b6944991c493ca4907e487df45f984553844cc144c4d448574452c42bd5420b8417744140d3e2b23d79c3d7123ceff3c4973c43e3b1753aa643976836b78353b934d8433fe631f72317bd30beb30b2b30318301362fa0a2f99c2f8672f4382f3532f0052ec432e9cc2e59a2e1512ddd02cab52c99b2c6212addc2a1be29fc1295fb28bf82849426e7f26dd826c59269fd2649125cfb25b5125b1e25ac32588624547241a92386e2324122ff62228b21dff21b9320bda2085a206b2206121f3591f22a1f15b1ece21ec351e4cb1e36a1e00c1d62b1cf4c1c92e1c8821c7741be411bd271b8281aac71a7861a4af19d8819bc219a4d1907d18f7318c4118c2418b3d189f81871017a39177531757d1724e1721b16ca21697f165ac162a515a6d1593b1591f155de15438152a314d6f14d0b1430613fc113c54
|7,2=>0xdb38eb273ea5311a36baa08629d5ba8fd01896c3880ee873bf78e7b784e277e4074b88728546dce1638db628db6201d611e35fd3a5cfba5ba985a9465a0c258c3f5878757e6c570e85535b5337f51b2d5036c
|8,0=>0xca924a5311a01738d66e8bac38225d7be357b04579d3e739a170c6f6dce06cf9a6a0e068bc166fc261632615505b3745891354d8e5250f4e9de4dc044c1e54be754aa0047c524793846cc045058418b03ff1c3eff73e4da3b62d383d23675d35006342e133e2732c5b316952e0c72d1672bfec2bb692a35f29956277b92608d259ef2541024bc323c2d213e72105820e2220d9820ce720a6e208ce1e92f1dcee1cc991c5191ac4119ab8158f41548214ed412bc511ab3116a61160610c26103c91010c0f77b0e6070d8b20d86d0ce730cdfb0bfe60bb7c0bb020b2cc0aea20abc60a9ed0a8220a6c40a22d09cda09bca09a2908f00083a50829b0785707724071320706306a98063d8058ac0570304a370499e046e103f3b03b10037bc02fc80222001ea301e5001a02019000174e01131008d0004e5
|9,0=>0xa965d9dc32837f67d02b6e11b5d8d357662572ac4dca34535b3ccb13afd1361333208030b612e1002b01a27a581f86a1b17c13dab111240b9a70ad9306e8203830017d9
|10,0=>0xb1a74379de1f24c0ebd0
|11,0=>0x59c84
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000a0a0a0a0a0a0a00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0f0f0f0c0c0c0c0f0c0f0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f000000000000000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a00000000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0c
|0,1=>0x303030303030303030303030303030303000300030003000300030003000300f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0c0f0c000000000f0c0f0cf0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0c0c0c0c0f000f000c000c000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0c0c0c0cf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f00
|0,2=>0xf0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0000000000f000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cf0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0f0f0f000000000f0c0f0c0000000000f000f000f000f000f000f000f000f000f000f000c000c000f000f000c000cf0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e0f0f0f0f0a0a0a0a0f0e0f0e0a0a0a0a0000000000000000000000000000000000f000f000f000f000f000f000c000cf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af030f030f030f030f030f030f030f030f030f030f000f000f030f030f000f00303030303030303030003000300030003030303030303030300030003000300f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f030f030f030f030f030f030f000f000f030f030f030f030f030f030f000f00
|0,3=>0xf0f0f0f0f0f0f0f00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f000000000f000f0000000000303030303030303030303030000000003030303030303030303030300000000f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f000f000f000c000c0f0f0f0f0f0f0f0f000f000f000c000c303030303030303030303030303030303030303030303030303030303000300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0e0f0e0f0e0f0e0f0e0f0e0a0a0a0a00000000000000000000000000000000f0f0f0f0f0f0f0f000000000f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f000000000f0c0f0c0f0c0f0c0f0c0f0c00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0030303030303030303030303030303030303030300000000030303030000000000000000000000000000000000000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f000f0c0f0c0f0c0f0c
|0,4=>0xf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f000f000f000f000f000f000c000c0000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f0000f000f000f000f000f000f000f000f000f000f00000000000f000f0000000000000000c0c0c0c000000000f0f0f0f000000000c0c0c0c000000000f0c0f0c000000000000000000f000f000f000f0000000000000000000f000f00000000000000000000000000000000000000003030303030303030303030300000000f000f000f000f000f000f000f000f000f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000c000c000f000f000c000c00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0000000030303030303030303030303030003000303030303030303030303030300030000000000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f000f00
|0,5=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0c0f0c00f000f000f000f000f000f00000000000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f0300030003000300303030303030303030303030303030303030303030003000303030303000300c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0c0f0c0f0c0f0cc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c00000000f0f0f0f000000000f0c0f0c000000000f0f0f0f000000000f0c0f0cf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0f0f0f0e0e0e0e0f0a0f0a0e0a0e0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f03030303030303030303030300000000f0f0f0f0f0f0f0f0f0f0f0f000000000f000f000f000f000f000f000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f0050505050505050005050505050505000505050505050500050505050505050000f000f000f000f000f000f000f000f000f000f000f000f000f000f000c000cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00
|0,6=>0xf0f0f0f0f0f0f0f00000000030303030f0f0f0f0f0f0f0f000000000300030000f000f000f000f000f000f000c000c000f000f000f000f000f000f000c000c0000000000000000f0f0f0f0f0f0f0f00000000000000000f000f000f000f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f030303030f0f0f0f030003000f0f0f0f030303030f0f0f0f030003000000000030303030000000003030303000000000300030000000000030003000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000f0c0f0c00000000000000000000000000000000f0f0f0f0f0f0f0f0f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0c0f0c0f0c0f0c0f0c0f0c0c0c0c0cf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0f0f0f0a0a0a0a0f0a0f0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000f000f0000000000f0f0f0f000000000f0f0f0f000000000f0c0f0c000000000f0c0f0cf0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f0303030300000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f03030303030303030300030003000300f0f0f0f0f0f0f0f000000000f0c0f0c0f0f0f0f0f0f0f0f000000000f0c0f0c
|0,7=>0x30303030303030300000000000000000303030300000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c00f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000cf030f030f030f030f030f030f030f030f030f030f030f030f030f030f000f0000000000000000000000000000000000003000300030003000300030000000000000000000000000000000000000000303030303030303030003000300030000f000f00000000000f000f00000000000f000f000f000f000f000f000c000c0000000000000000c0c0c0c0f0f0f0f00000000000000000c0c0c0c0f0c0f0c00f000f000f000f000c000c000c000c000f000f000f000f000c000c000c000c303030303030303030303030303030003030303030303030303030303030300f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cc0c0c0c0c0c0c0c0c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0f0c0f0c0c0c0c0000000000000000000000000000000000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f00c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0c0c0c
|0,8=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f030f030f030f030f030f030f000f00f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c505050505050504050505050505050405050505050505040505050505050504f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0c0f0cc0c0c0c0c0c0c0c0c0c0c0c0f0f0f0f0c000c000c000c000c000c000f000f000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0af0f0f0f0f0f0f0f05050505050505000f0f0f0f0f0f0f0f0505050505050500000000000000000000000000f0f0f0f0000000000000000000000000f0c0f0c50505050505050505050505050505000505050505050505050505050505050000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0c0f0cf000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0c0f0c000000000000000000000000c0c0c0c000c000c000c000c000c000c0c0c0c0cc0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00
|0,9=>0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000f0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0c303030303030303030303030303030303030303030303030300030003000300f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f000f000f0f0f0f0f000c000c0f0f0f0f000f000f0f0f0f0f000c000c00000000000000000000000000000000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0c0030003000300030003000300030003000300030003000300030003000000000000000000000000000000000000000000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000c000c00f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2a0d04290e0a0c0b11190a24280c041c210e0a0f262107151805100803181305102521140a2411072305220d210720051f0c040e18051e0d11191d18050b121c07030a0111030a090c04030a0f000c04031b05000c1a1119151805121707030a0104081615130504141301000b120706050d08030a0908070603050403020100
|1=>0x2707030201111902012d0b381119140a241207370a0c0b040e0a24360c33271935240c1207340a050d330807160a0f272119140a0f272119141b050411161431242708190313010819030a0132251918052d0b08070e31242d0421300e0a011107031d0a012f1a07030a012e1913052d0c27072b0e050d1008030a0f11191805
|2=>0x50d2f21071613012721191413010807060e050b12070532220d2f2707160f0b08072b030a052721073514011207060a050d2f1a0716050d1a0819030a01211913053b0c042b0e0a240c04210e243a0c272507351405262107140a0f381107161424262107141b0508070603052f21070a011f11191d0a050d11191439010b12
|3=>0x8160313050c1221073518050c121a07150a050c3c1119030a240c1207053d1f0c0b100803180a050b4011071613050c3327070e02050c330821070e0a0f11193f030a240c1025080e0a010b2608070e31050b120706050d1a08072c03051107060e050d080706030a05210714053d1f1107031d1805042f25030a01123c0735
|4=>0xb121a210716240c2e190a052d0c0b271119141b050b2711192c14010b3311071618240c10110e0a02010b25111914130a051a11190318050c1107030a05420d2f270735050c0b11190a243b0c0b10210e1b0a050c1a11071614050d21110735140a011107161824410c331a110716240c0421160e13010c1211072c13050d04
|5=>0xa240c1207140a01320b1107031824000c2721072c03050c2708190e0a0f0b123807140a050b3311072c0a240c2708190e1b050b3c0821070e0a0f121a0716010c0b4511070e0a010b1221071618240c11072c0a24410c082107350e0a0111191805440c0b12072b0a050c0b3c21071614050b2743072c0e050b271119140a0f
|6=>0x19140a05490b1107030a242a0c081107480e0a242f1107161b050b1021140a050d2621070318050c4711071613050c11191b052d0c0b1107060e0a050d33251107140a24120807160a0f0b0408460e0a050b2621071413050c120807161b050b1221072c0a240c040e3105000c0b2643070e18050b2f270716240c0b04331a0e
|7=>0xb08070e1b0a054c1a080714030a05040e0a054b0c0b1119140a014a0b1107161805410d08070e13052d0d2107340e0a050c0425210e18130511072305220c0b2f11070318130511193f030a050d210714030a053d2f070e0a01320b110716150318242f1107160a0f0b1208070318130512252107140a2411191514130a0111
|8=>0x1614130521111914130a0125081119030a014d270716050c0b1221071618050d33080714030a2411072c0a05410d04112c030a240c27072b0e050c0b11193f150a050b111918052a0c0b0421140a051f0c3c11071603240c3311071618050d2721190e18050d2f1107030a0f044316140a050b11190a053b0d0b04113f0e0a01
|9=>0x1107141b050b10210e130a520c0425140e130a052511072c030a0511190a05510c0b102115140a050c5027070e18050b110735150e182411070e053a0c0b1a11072c03050c0821190e130a011221072c0a050d11070e4f0a240c11071618244e0b2f270716050d0b1a0821070e182427110716140f0b270819030a010b251107
|10=>0x570b251107030a05222708071603010b1107560e0a0c0b211107161413013311072c13050c1221070a05220d1221070e0a02010411161518050b110714030a05553311070a05220d3311070e0a0201210714540a0504112c030a050d0411030a24220c27070e13054a0c5327070e18050b11190a05280c0b33080714130a0526
|11=>0xb0411030e0a020112210714180a241011140a0f0b260807030a010b272107140318053c1107350e050d122107590a050c042508030e0a01121c070e0a010b04081403130a05110e0a090c0b082119150a052107030a05420c082107160e130108070e31052d0b1119030a0201581119140a050b272119150a050c0819140a05
|12=>0x140a050b1107160302015811071614050b125e07030a050c1211071631240c101135030a240c5d11070e0a010b2711190e31240c2111070e39240c0411161431050b21070e180a245c2f21070e180a24111915053a0c0b1221070a055b0c04112c0313050c11071418051e0b43070e18052d0b0411030a05220d1107140a015a
|13=>0xc1207650a0c0b121c0716050c0b11070e1813056412080715130a052711191413010b5e11071614050b10030a05630c0b262107150a050c1008030a010b1119140a01320b381119140a050b1207140a05620b12170716050c0b04210e0a05610c041c210e0a010b1107030a24600c040e0a05360c0b331119150a240c5f0807
|14=>0x5e210e0a240c3311070e39240c041114030a0f041114031813050421030a05220c04030a05570c0b1107140a056a0d2f27070318050b1107140e013a0b11070e0a01690b1107140a0f411107030a05600d1107141813054108070e0a0f2d0b1107141805630b501119140a010b12270767050c0b2107660e0a050c3327071624
|15=>0x7060e050c0b1107060e050d11070e39050c0b082119030a012708190e18240b10110e1813050d12073e0a050d27110714030a0f10430e180a050b260807140a240b1008140a520b11076c3f0e0a05120807031b0a05110714053d1f0b211107160e0201401107140a010b12270746050c0b6b1107030a240c0807060e050b04
|16=>0x5410c043c250e0a050c0b122508070e0a010b380811070e0a240c3c11190a056e0c0b471107160a050c0b1107140e0a05620b12080714130a050b171107160e050c0b271c11070e18050b3308070e0a240c041135140a050c0b211107460e0a050c262107140a050c0b1711070e0a010b122107140a240c50270716050c0b11
|17=>0x1211070a051f0d0c2f2511070e0a010b041a210e18050c0b041116030a240c1c11070e0a010b112e0716030a050c0408350e0a050c0b3311070e1b0a050c272107350e050c271119030a050d0c110714540a050b12210735130a050c12080703180a050b04210e1813050c501107030e0a240c381a11070e0a050c11070e1b0a
|18=>0x19140a050b1221070e1b0a050c0425210e180a050b7121070e0a050c0b041116140a240c0b04210e0a0f0c272521070e13050c1107650e0a0c0b1c1107160e050c0b1a111903130a050c2f21070e0a240c111914130a010b2f110703180a050b11070e700a050c0b11070e0a056f0c0b08110716680a050b081107150e130a05
|19=>0x27072c18050c0b1119031b0a050c1a2708070e18050b271107670e050c0b0408160e0a240c0b5f11070a052a0c0b2107350e0a05630c042115030e0a050c2711072c0e050d0b502f11070e0a010b2f0811070e0a0f0b3327210716050c0b08070e0a052d0d0b11192c140a050d0b1211070e0a02010b21070e0a245c0c3c0811
|20=>0xa05750c0b1a08070e0a010b2f110714030a010b7411190e0a050c0b25110716140a050b0821070e180a241208070a05220b2711070e6d13050c1107160e31240c2611070e18050d0b1107140a05410d041114030a240c1107030a05420c0b081107160e13010b1a11071614050c0b11070e730a050c0b271119150a050c0b12
|21=>0xc11190e0a05550c0b0807140e0a05320b122107140a050d3327070e0a050d0c271107030e13010c04080e0a056e0c0b0408030e0a240c5011070e130a050c11070e1813054c0c1a0807160e050c0b121107590a050c0b2611071418050b0433210e0a010c0b111946150a050c0b331107140a050d1107030e0a01320c10110e
|22=>0x121107350a050d0c270807030e18050b042f080e0a010b1107060e0a050c0b1021030a050c11072c140e13010b211107140e18130512110714180a240b25110714030a050411030e1b0a050c0811076c0e0a050b380811070e0a050d112e07350e0a050c11070e0a0f4c0c2708070e05760b271107140318050b272e070e1305
|23=>0x13010b3311071613050c2f11070e180a240b2721190e13050c2f081107030a010b2711071603050d0c1119130a052a0c0b11193f030a050c0b11071615140a010b11070e0a05780c0b2f11070e053a0c0b1211070a055b0c0b1227070e31050c0b3c110716056e0c0b11070e770a050c0b1021140a050c0b5f1107030e0a240c
|24=>0xb1107031305000c11070e0a016a0c0b121a210716050c0b11070e053a0c0b11077b0e0a050c0b3311071618050c0b041114030a050d11070e0a057a0c0b1221071613050c27070e0a054a0c0b0811070e0a05790b3c0811071614050b331a110716050c0b04110e310a240c08070e13052d0c0b11070e180a245c0b11071614
|25=>0x460a050c0b11076c16030a050c1221072c0a050c0b04210e0a057c0c043c08140e0a050b04331a0e0a050c0b21110716140a010b3311072c0a050c0b1107160a014e0b12210715140a050c04210e0a02050c2711190e02050c0b1221071618050c0b3c3811070e0a050d110716030a0f0c2711071615050c0b11070e0a24420c
|26=>0x70e0532220c0b272107030e0a010c12070e0a057f0c0b043c080e0a240c0b110716150318050b10110e130a010c0b12270735050c0b21110714030a01112e190e130a050c1107030a052a0c0b081107480e0a050b11070e0a055a0d0c11070e130a057e0c082107160e0a010b7d1119140a050c0b33251107140a050b121107
|27=>0x50b3311070a05220c0b831107030e0a050c0821070e181305124307160a050c0b27070e0a05820c0b33080714030a050b8110110e0a010b1a11190e18050c0b08110735140a050b0425080e180a050b12270716240c0b3c11190e0a240c0b1107160a05800c0b11070e0a02054c0c10112c140a050c0b11076c14030a050c11
|28=>0x30e0a240c2107140e0a053d0b3c1107350e050c0b2711190e13050d0c10110e0a870c0b042f08030a050c0b2621070e18050c0b11190e0a05320d0c33211107140a010b11070e0a05860c0b1011030a050d0c271107460e050c0b8511070e0a050c0b1221070a05220c0b11070e4f0a050c0b11070e05840c0b2511190e180a
|29=>0x50c0b11070e0a01630c0b0443140e0a050b11070e0a8b050c0b042116140a050c0b21110e0a0f8a0c04210e0a051f0c0411160e18240c0b1211071613050d0c10110e0a890c0b1107140e310a243c11190e0a050d0b2f2719140a050c0b11070e0a05880c0b1011150a050c0b2611070e02050c0b1227070e0a0f0c0b270807
|30=>0x1107300a050c0b123c072c0a050c0b2111070e39050c0b122107160a050d0c10110e0a8d0c0b0411670e0a050c0b11070e3e0a050d04110e0a24220c0b1107160a05410d0c110714031b0a051107030e0a05620c12250807140a050b1107150e39050c0b122707030a010c0b1107150e1813051107030e0a243d0c8c11070e0a
|31=>0xb08210716140a050b11070e0a056e0d0b5f11070e0a010c0b11070e02052d0c0b1a0821070e0a050d2f070e0a05570c0b04250e180a050b11070e0a05910c0b11070e130a014e0b11070e180a05900b1107150a05000c0b11078f0e0a050c0b211107160e0a0f0c0811072c030a050b0421140e0a240c081107160318050b12
|32=>0xe053a0c0b2611070e0a0f0c0b2611070e1b050c0b111935030a240c11070e0a053a0c0b271107160e0f0c0b12270716050d0c0b0811190e0a0f0b5011070e053a0c0b2711190e1b050c0b0811190e1813050b1119030a05930c0b08210714030a052f11070e130a050d9211070e0a050c0b122707140a010b10110e180a520c
|33=>0x1a11070e0a052a0c0b10110e0a240c0b2611070e0a010c0b2f1107150e0a050c0b2711070e6d0a050c0b1107140e1813050b1119680a050c0b5011070e39050c0b1107060e050c0b5011070e0a050c0b0811190e310a050b11070e0a05940c0b10110e0a02050c0b11070e39050c0b10110e0a0f0c0b110735140a050d110703
|34=>0x50c0b110796140a050c0b0411680e0a050c0b5e0811070e0a050c0b1107160e13050d0c1107030e0a05630c0b1107160e05950c0b25081107140e0a050b081107030e130a050c081107030e0a010b272e070e0a050c0b11070e0a053b0c0b271107030e0a010c0b1107140e0a0f0b12070e0a053d0c0b2f081107160a050c0b
|35=>0x35030e0a240c040e0a05000c0b1a2511070e0a050c0b2711070e0a0f0c0b2111190e0a010c0b2721190e0a050c0b04112c0e180a050c0b2711070e1b050c0b2111070e0a05720c0b2511070e130a050c1107160a05410c0b3c1107160e18050c0b11070e0a05640c0b331107030e130a050c5f1107350e0a050c0b9711070e0a
|36=>0xa051f0c0b122107140a050c0b11070e0a05490c0b122107030a050c04110e130a050d0c331107140a050c0b11071403130a050c110714030a010b1107140a05410c0b1107030a05000c0b08110715030e0a050b331119030a050c0b122107160a050c0b11190e310a050c0b3c11072c0e0a050c0b211107160e0a050d0c1107
|37=>0xa050c0b271107140e0a010b1211070e130a010c0b11070e0a05900c0b11070e180a056e0c0b2621070e0a050c0b1107030e180a240c1221070e0a240c3311070e0a240c332111070e0a050d0c1107160e31050c0b041114030a050c0b1a2111070e0a010c0b1a11190e0a050c0b04080e0a010b501107030e0a050c0b04110e
|38=>0xb1107990e0a0f0c0b11070e980a0f0c0b5e11070e0a050c0b121107150a050c0b0811072c0e180a050b21110735030e0a050c121107030a050d0c5811070e0a050c0b110735030e18050c0b1a1107160e050c0b121107160a050d0c0b0811190e0a050d0b0411160e0a240c0b110e0a0f8a0c0b1119140a240c0b1211072c14
|39=>0xe0a053d0c0b1243070e0a050c0b10110e0a050d0c0b11070e0a059a0c0b11070e3e0a050c0b110716030a010c0b2725070e0a050c0b041115140e0a050c0b0411160e13050c0b08110714030a050b27110714030a050c0b111915140a050c0b2611070e0a050d0c0b2708070e0a010b11073f0e0a050c0b271107160e050d0c
|40=>0x411150e0a050c0b11070e0a05620c0b9b11070e0a240c0b3c2711070e0a050d0b11070e1813050d271107140e13050c0b271107030e13050c1107030e0a05320c2f11070e130a050c0b11070e0a052d0d0c0b12110703130a050c1211072c0a050c0b11070e0a05720c0b501107150e0a050c0b7d11070e180a050c0b110703
|41=>0x180a050c0b1227070e0a050c0b9d11070e0a050c0b3c0811070e0a050c0b11070e130a010c0b1107150e0a050c0b1211070e0a240c0b1107030e0a050d0c11190e1813050c0b5011070e0a050c0b2708070e18050b11079c0e0a050c0b1a1107030e0a050c081107350e0a050c0b5e2511070e0a050c0b33110716030a050c0b
|42=>0xa050c0b10110e0a050c0b2611070e0a050c0b1a2711070e0a050c0b271107160e050c0b1211070e0a050d0c0b11190e0a240c0b0411030e0a050c0b11070e0a05220c0b1119030a050c0b1107140e130a050c0b1107030e130a050c11072c0e0a050c0b1107160e18050c0b4311070e0a050c0b2f1107140e0a050c0b11190e
|43=>0x11070e0a050c0b11190e0a050c0b11070e0a050d0c0b1107160e0a050c0b2111070e0a050c0b110714030a050c0b081107030e0a050c0b11070e0a052d0c0b1211070e13
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x728029000aa0005
|5,0=>0xc53061182fcc17860b9305b182ccc16060ad30551829cc14860a1304f1826cc130609530491823cc1186089a8435820ec101607db03d581dec0e96071b037581aec0d16065b0315817ec0b96059b02b5814ec0a1604db0255811ec0896042281f980f0c07260363019980c0c05a602a301398090c042601e300dd4062c02b6012b007d8032c0136
|5,1=>0x1a850d130671832cc1906
|6,0=>0x1b2b8d7d86b0e35171a538d0dc678e335719738c9dc640e319718938c2dc608e2fd717b38bbdc5d0e2e1716d38b4dc598e2c5715f38addc560e2a9715138a6dc528e28d7143389fdc4f0e27171353898dc4b8e25571273891dc480e2397119388adc448e21d710b3883dc410e20170fd387cdc3d8e1e570ef3875dc3a0e1c970e1386edc368e1ad7
|6,1=>0x29239475ca2ce50f728439405c9f4e4f3727639395c9bce4d7726839325c984e4bb725a392b5c94ce49f724c39245c914e483723e391d5c8dce467723039165c8a4e44b7222390f5c86ce42f721439085c834e4146206b9019c7fee3f871f8b8fa9c7c6e3dc71eab8f39c78ee3c071dcb8ec9c756e3a471ceb8e59c71ee38871c0b8de9c6e6e36c7
|6,2=>0x36eb9b59cd9ee6c8736131aedcd68e6ad735339a7dcd30e691734539a0dccf8e6766337b99a1ccc2e65a7329b9931cc8ae63e731bb98c1cc52e622730db9851cc1ae60672ffb97e1cbe2e5eb62f239775cbace5cf72e439705cb74e5b462d73169dcb40e59972c9b1631cb0ae57e72bbb95c1cad2e56272adb9551ca9ae546729fb94e1ca62e52b6
|6,3=>0x2005cff4e7f463f6b9f9d8fc0e7d973e9b1f31cf8ae7be73dc31ec5cf54e7a373ce39e55cf1ce78773c0b1de9cee6e76d63b339d7dceb0e75173a539d0dce78e7366397b9ca1ce42e71a7389b9c31ce0ae6ff637cb1bc9cdd6e6e47
|7,0=>0x4f93a7aa13c509da84e94272a138509ba84d9426aa1345099a84c94262a1306e97b84b9c25ae12c7095b84aab2536128ce93e849b424bdd250e920848c4244212110900847c423c211d108e1746d3a34a119508c2845dba2ce1158e8a4844e42255d11b0885843ec21d610db0865842ec2156109b0845841ec20d6105ce826840f4205a101ee8087
|7,1=>0x5efc2f5e179f0bc785dfc2ede175f0ba785cfc2e5e171f0b8875c042de216e10b6975b0c2d6d96a70b4b85a1c2cf1d6690b2c859242c72162aeb0e758342bfdd5ef0aef85743ab8215b10ad08564bab0615730ab18554c2a89d5350a928545baa0e14f70a7475364299214b90a5575273a91a147eea3785183a8a5d4430a198508c2826140309f98
|7,2=>0x6e7c3721db810db886d8436a5db430d9986c8c36261b030d7986b8c35a61ac30d5986a8c3529da86ed3b8699c34ae1a470d1b8689c342e1a070cfb8679c33ae19c8ecdc866a4333219890cbd765ac32b9d94d0c9e864b4323dd90f0c7f863c3b1c218d10c61762cc31461894ec42861dbb0ce18570c23860dc3051d8190c0485febafd9d7dd0be77
|7,3=>0x7e043ee21f610fa887d043e621f210f8977c0c3de61ee30f6987b0c3d69dea50f4b77a1c3cee1e68ef2c879243c721e290f0d7782c3bf61deb0eee777343b7a1daeeed0776443b021d72eeb2775543a8a1d350e937745c3a0e1cf70e738735c398e1cb8ee548726439121c790e348716bb8961c3b0e158706c3819dbfd0df686f74379ddbbf0dd78
|7,4=>0x10bf885c3c2c2215110a0884c44245e114f083783dc41ce20d71064782e4415220991045781ec40d6205b1025880f3c05a201d100777ffc3fde1fdf0fe787efc3f5e1f9f0fc87
|8,0=>0x96544b0de578f2b39955c4a8e25353292894634a0e64f712738935c4991e4b91254892644915e47b123589164c892243912148905cc80a63f511f378f54c78a23b511d288e4cc706237131b088d44467e632f118e98c2cc5f622eb116d88b24c57222a7314b88a14c4e6626311298890c44626222f10988804c3de61e0f0e8886fcc35a619d10c77
|8,1=>0xa5d452ca2956f4a38a4dc524a691334809a3c451c228d1145f9a2c3d13e688f143f8a1b4d0b6684b141d8a0ac5032680733fa99f944faa27c513da89e944f2a278333b989d8c4ea26741139799c83ce2226ff337789b7c4d9e26bf135699a6ccd16267b1334999644c8e6637131389863cc15e5f932f48975ccb8e25b532d28
|9,0=>0x565a2b1b35858abe4d5d5eadb15649aae4554e6a98f5448a9e454d5ea5935248a8e454522a1915039a7dc53ce29d714e29a6d4534a299514c28
|10,0=>0xadb3d6ba2b4d159e8
|11,0=>0x15bd7
|_,_=>0
def wAt:=mkWire dB 158 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x50c41c450b0a430450e0b4502d2e0e48433110b44431050d4442d0c0b430150712430450e114f82921140302d0c0e42c450e1146850080e4143107114202d110c43845050c41c390b0a43039110b45045210c44c310a0b40c29070e4440d0b0e4142d141a038452c210302d0e114389d0a1145068100f0382d050d4302d0712438450c0b44431100f0382d050d4302d
|1=>0x50c42c510e0c4282d070e4602d0a0c4302d1207430390b1143845050b48431210e42c450e1b4602d0a0c4602d0a0c4142d080e44431210a41c45050b484390b1144439130c4282d070e43091080a4142d0b11430450b2742845050c484b0140a430390e07414350e0c42c31050b484290a0e42c45050c42845070e450290c0e43845110e42831050b48429210e42c45
|2=>0x210c4481d08034382d0c1140c31050b40c290e0b41c39033c044610a0c42831050b48429110b414310b0c4442d050c438310a0b41c39070e4142d031142c390c11438610a0c41c452c21058310a0e40c45070e42845080e43415110c4382d0c0b438290a0c49c3b0a11420d40e134282d0c214442d0a0c41c45141142c390a0c4142d0c034382d050b484310b1143039
|3=>0xa0e44c330a0b42c390a0e41431430a4202f110c4204d0a0b43045050b40c29071242c39110e458310a0e41c450e0c414350b0c41c490e1142c39050c41c45080b44431100f014350c0b41c490e114381d140b444310e0c4442d0e0b41c39050c4304e0a0b42c310e114442d140b43831071142cf5080ac3045110b4383108030382d110c438610a0c41c450a0d4302d
|4=>0x14210442d0e0c41c450e0b414350e0c42c310711438311103814350e0b4302d000c4445a0a0e43029680a4502f0e0c4482d110e428390a114142d110e4f815211403831110b42d391411c3039110a414310e0c4282d070e48461110b4283119114d447120a43845050c4481d0b0e430450e114c831210ac2c4511024304e0a0b40c31070e4142d031142c39113542c59
|5=>0xa1142c490b05430450e114384d0a0b41c451413438310a0b40845050c4304e0a0b4142d0c0e42c450e11448350c0b444390c0b4f829211403831110b4442d070e41431110c4382d050b444310a0c41c39071242c290e1142c3121140302d0c0e42c450e11434150e0b438310b0c49c390a114142d0c1141442071243039110e4602d0a0c458350a0e4302d110c4f829
|6=>0x50b468330b2742845050c428390e134282d0711428350b0c40c290b0e4442d0a1142845070e4382d0c0b4383108030382d110c444390e134282d110b4282d0a0c41c450b274f02f270c42845080a41c45080b44431080b414310c11438450b054f02f080a4f03b111842831070e5b445030cc382d320c4842b110b430450b0a43039110e408450c138282d1a0cc9c2d
|7=>0x110e414310c138282d0b114142d080ec3045080a41c390e0c444310a0d42c310c214442d0a0c41c457211484520c0e42c451107430390a0e4142d0d0541c45110b4302d0a11484310b114282d3e05484500e0c4442d1a0cc9c2d0a114382d11134282d070e44831050b42c450e11414310e0c4282d070e41431080b420390c1148429110b42831071141c450b0e42839
|8=>0x1116428390c0b430390311c2c39050b4441d0b0e430392f0ac3049110e4282d0c1142839050c434390a1141c390b0c46039110e428310b0e44c310a0b41c39270b444290c1142831680a4502f0e0c41c450c1142839050b4386a1a0e44c450a0b4d4470e134282d07114442d0e0b44831050c44439050d444310b0c43829210e4442d270ec4429140a41c390e0c42c31
|9=>0xa0b430390c0b430390b1143845050c41c453c0ec20290c1141c45050b4382d110c49439210c42c450c0a5b429030cc382d1611430290e0c42839050c41c450b114381d0e0d4302d210e4442d0e0c42c31050c4842b0b11430450b2742845050c42c39050c450450c0e4c4450b18828310b084142d110b430450a0c44431140ac3039110e444290a0e4142d0b1882831
|10=>0x1a0ec4c45070e4d433030a4382d050c42c510e0c428391f0c40c2b0b0e42c620a0c4f03b270c428451207430390b1143845110a4382d0c1142831071141431080e430450b0e41c490b11438450a0b41431140a438310a0c4142d080b43831110c4382d130c4282d07114b02f160c428393c0bc2029110c43886050d4442d0c0b44431180ec28450a0c48433110a42c45
|11=>0xb14458470b0a4382d0a0e484290a0e42c45500ac200d0e0b44431250ac44350c0b438450e0b4441d0e0c42c310b11438450a0e4282d142183039110b4504f0c0e4282d080a430450a0e42839210a484390b1141c45050b42c620a0c4142d080ec30450a0b430390a0e414310b12438450a0e4282d120c4142d110e42845110b4282d070e42c39050c420390c1141c39
|12=>0xb0e4c4390b1882831330ac440d0e0b42d71080ec3045110b430450a0e41431070e430390e0c48431210e42c451b0e428350b0c4b02f160c428390b114384e0a0b41c45080a41c45110c43831071148429210e42c45050c42c450e0c428390311450470c0e42839050c4502d0c0e42c45110b44c330a0b41c45130cc282d070e4f02f270c428450e0b430910a0e4142d
|13=>0x4c0c4843b0b1140c450b0e43045100c4143107124384511134282d070e41c45080b430450a0c444390a0e42845050b4142d111842831070e444560e0d4302d140a41c490c0e444392c0bc50290e0c430152118c30290b1142c150711420290c11430290c034382d0a0b41431071243845130e444390a114282d0c0e430150e0b4442d0c218442d070e57c3b330a40c45
|14=>0xa0c444610a0c41c39110a41c391411430390e0d4302d0712438450a1143845050d4302d0b0542c39110c428450e07428450581840310712444390e0b41c45080e43045070e4842b110b43039050c484390b114382d0c0b41c490e114d431160b428390b1140cf0111842c390a0c5502a08030382d110c41c39080b430452e0a48433110b42831110c42c450a0b43829
|15=>0x210e4163a100a41c490e115a029140bc3831211403831110b4302d130c438310b0e4282d320c4842b0b11444390c0e4202d110c414310a0c40c310b0e4282d050b4202b110c4d4470b16428390b0881c45110c43831033dc382d110c41c450b11438310a0e41c3e050d4442d0c0b41c450b1140c2b0b0e4142d0e0a428310711431491005c1c490e1143039050b42c62
|16=>0x70e414350c0b4200d0e0b44431180b42831070e41c39110b43831110c4382d141144429050c43039110e440170712438453c0ec60450a0c4982d1611428390c1148429110b4302d11144b047140a4303911074202d0c1142831050c42c291411c3039250ec202d0c1143829050d4442d0c0b43831110b4142d0711408390c138282d110e46045180e42831500a0cc31
|17=>0x80ac30450e1143829080e430451a0ec4c450a0b4142d071243845161142839050c4502d141143039110a40c330e0b4282d0c0e428310e074502f0e0c4f829211403831110b42c620a0c41c39500a0200d0e0b44431050d4302d071243845130e4282d0e0c42c31500accc310311428350b0c41c39050b40c290e0b414350c0b444290a0e444290a0e4302d110e43045
|18=>0x180b428310a11484520e0c484310b114282d0311c382d0a0e428391811428314e0b450470c0e4440d0b0e4282d130e4282d76114603b0a0c42c5a0e0c4283907114502f0e0c49429080b444310b0c4282d0a0e4d447030a42c391811c28390a0c43039080b44431110c42c390a0b41431110c4382d0c218442d0a114b4310e27828450b0e42845050c414350e0c42c31
|19=>0xe114204f0c114282d0b1142c39110e42c310a0b41c450b1243039110e438310b0e4282d050c430390b0e430390311c2c391611c382d0a0e43045030c4382d070e40c450b0e428390b1143845180bc2831070e46045180e428310e0a4442d0c0b4142d030a4382d07114445a0a0e48429210c4442d0c2442845050b4442d050c41c39070e4442d0a11438610a0c41c45
|20=>0x110c42c31071142839050b43c1f050d4302d0c0e41c39050b450290c0e444390c0e42845050c4282d050c444390e25844350c0b4f03b1811428310a1242c450e114142d0b0e42831050b42c450e114482d050b444390e214442d0c0b428390b1882831110742c390c0e41431210a4442d11134282d070e44431050c41c45330c40c450b0e41c45030ac2c390c0e42c45
|21=>0xb08444310a1141c45140b438310e0a4282d071143831110c4382d0b0e438310a1141c39140b438310a1242c310e11430450a1141431350cc582d0a0e4302d110a428390f0e414350b0c43c29050d4302d0813430450a0b4300d0b0e444390e18430450a0c42c45030a42c39110e4382d0c0b50c29080bc4431030a42c390a0c49c2d0e0a428450a0e4302d110e4381d
|22=>0xe0b428390d0e41c450b0c4c831210ac442d0c2782845050b42c31270c428450b0c42c290a0c444290c0e4282d110a42c390a0b42c39210ac2c451114430390a0b4302d0e27828450b0a42c39110e450290c0e44439211483831110b438350c0b4b045180e428310e0b4202b110c42c220c11438450c0b41c490e114542b0e0d4302d211403831110b42c390a0e41431
|23=>0xe1149c2d0a11444290a0e444390c0b4142d070e4382d07114502b0e0c4382d070e430390a0b42c390a0b458310a0e428310a0e4202f110c450450c0e42831070e428450e1149c2f0a1142029110c42c29050c438350c0b4142d110e4382d0c0b4282d0a0c41c3908034382d110c444290c11428310d16838290c0b4444d0b0e4282d0e13430450a0b444350c0b40c45
|24=>0x1c390c0b42839110b42c390c0e4382d110c4389e0a1142c29110e41c490e1142849
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x140000000
|5,0=>0x50208d4000022103aa000000000000000000000001c100000000000000003620000000019200000000000000000000000000000000000514000000000000000000000000000000000000002620484000011101e4000000000000000034800000000000000000000c100000198000000000a200000000000
|5,1=>0x296000000000000000
|6,0=>0xf241d1400000000000000038200000da600003590000000000003418635000000000000000000018842f985a50ae600000000000000000002a18000000014102620000000011d42308000000000000000451000000000000000088210101f88000076800001d08000000000001b980000668000017a0000
|6,1=>0x18460000000000000000000601000000002fc40000be117662dd0000000016c20000599800000002bd00000ae115a22a145388000000028d00000a0313a600000000000000027044d109551282000000000000000000000009311224238c45200001122000044080001088000000008040f6a00000000000
|6,2=>0x232a458c8a1112221aa000000010a320e600000000000000040947f98fa51ee63d0c0000ef50000000000000000000000000000001d8600000000000000000000000e750000000000000001c4a00000000dd51b0a000000000001a6a000069080000000000000000001a2234040000cd3194600000000c55
|6,3=>0x5a8c000165500005814ae215842a6a53d000014c328ea0000a29000000000000a11800027aa0000000138526e20000000000000000000000132525e64b84000000000004acc0001265242a00008f18000
|7,0=>0x448888110e9a19442a8848d07980004186824d031a04240087f10fc21f443e447b90f521e643c487790ed21d733a6873d0e5a0000000000000000000000071d0e1a1bf437686e84db99b5236286b50d4a1a630000689000019e400006690cb2193331e8630cc49985430465fccbda17832ea60000b8a16d4
|7,1=>0x582800015f1aba456c800000002b335624ab8c0002aa4000000015322a240000a7914d200005304a511489a8e35166000143a283400009fd000027e14f4800013c8a7544e289b8d36880004d469991319a6034b88964c00025544a28938d268a49448a8910520223e247488d91199a2f40000000115a2283
|7,2=>0x6f46dd91b9980006de8dad1b3a36430000d811ae980006b82d64daaa352369c8d291a32343367e8cf0d9c9b3636648cc09962329364c6000191231e46348c5918a8b11461c6c29183980006086c0117f880005f6800017c1af445e26bc0576200005d08b94d711adf35b68b5d00002d435a08b311649ac54
|7,3=>0x1051208980000001035000040940001018e0123ff30000fed1fc1bf4400000001f823ed37d280001f40be447c260001ef1bda47ae6f4d1e7a3cb478e80001e1a3bf47786ee100003b440000ec11d6200000000ea89d323a240000e7cdcda000072e8e50c000393171e8e2d1c41800070a6e051c00b7d3
|7,4=>0x8c2800022f18000000116922b2452489e6000226944940001115220a43d487470dce1b0800086490c4400042d485460002139c243000108120e24184
|8,0=>0xa407474e8d1d173a287444e871d0b3a107414e811cff39f873e4e7b1cf339e073b4e751ce739c87384e6f1cdb39b07354e691ccf39987324e631cc3398072f4e5d94b8396a72c8e579cac3954529ce521ca1393c726ce4c1c953924723ce461c89390c720ce401c7d38f471dce3a1c7138dc71ace341c653
|8,1=>0xba4773cee61dc93b8c770cee095be3b7676e0eda9db23b5e76b0ed49da63b467680ece9d9a3b2e7654ac91d8f3b187624ec31d833b0075f4ebd1d773ae875c4eb71d6b3ad07594eb11d5f3ab87564eab1d533aa07534ea51d473a887504e9f1d3b3a7074d4e991d2f3a5874a4e931d233
|9,0=>0x1824b0396052c065804aff95fd2bf657e4afb95f52be657c4af795ed2bd657a4af395e52bc65784aef95dd2bb65764aeb95d52
|10,0=>0xc1c38347060e0b1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x18400000000001800000000000154100000000010f000000000010800000000001040000000000103000000000010200000000001010000000000100100000000010000000000000880000000000085000000000008400000000000800000000000070100000000004f100000000004c100000000002000000000000120000000000010000000000000e000000000000c000000000000a000000000000800000000000041000000000004000000000000200000000000010000000000000e00000000000010000000000000
|1=>0x7cc9000000000700e0000000005fc10000000005ee00000000005dc10000000005cc90000000005cc10000000005a1100000000059d1000000000590000000000058e000000000058cf00000000058c000000000055c500000000054c100000000054c00000000005051000000000504000000000050000000000004a51000000000490000000000048900000000004880000000000481000000000048000000000004680000000000404000000000040000000000001c810000000001a4000000000018700000000001860
|2=>0x400800000000040000000000003e844000000002f6400000000025cc100000000240000000000020a00000000002080000000000200400000000020000000000001f4c5000000001800000000000150cd00000000118000000000011000000000001080000000000101010000000010100000000001004000000000100200000000010000000000000fec1000000000c810000000000c800000000000bed100000000098d0000000000981000000000088800000000008800000000000824000000000080100000000008000
|3=>0x145ce100000001348a50000000115da5000000011496900000001108080000000105ec1000000010400000000001010200000000100cc00000000100a65000000010040000000000d18a800000000cdcd100000000c9e5000000000c9c50000000009dcc900000000980c400000000870ce000000008000800000000656c100000000607010000000057cc90000000055cc90000000055cc5000000004b4000000000045cc100000000455c1000000004474100000000410000000000040a0000000000408600000000040800
|4=>0x301200000000030100000000002c5cc100000002c14c00000000255dc5000000025508d00000002501c00000000245cc100000002454c50000000245140000000024100100000002410000000000240d600000000240800000000022a8100000000225ec100000002257010000000221e110000000214100000000020f4c400000002092400000000207c090000000205dc10000000205cc90000000205cc500000002057c10000000204200000000020400000000002018d0000000020080000000002000000000000185ce1
|5=>0x4209440000000201c00d0000001899088000000108b444000000066000000000006454c1000000060f4400000000605cc10000000514805000000048dcc1000000044808000000004454c10000000441a4000000004400400000000425900000000042154100000004211c0000000042080000000004155c90000000410040000000040e6c00000000405e410000000405cc100000004058c000000004056c10000000401441000000040028000000004000000000000344ce10000000307cc10000000305ce10000000301ec1
|6=>0x1010184000000100408800000010021ed1000001000fcd50000010005cd10000010004dd10000010004cc5000001000480000000100018000000010000080000001000000000000085204200000008427c20000000840008000000084000400000008207ce10000008144ce10000008114ce90000008105de10000008105da10000008100d6100000080400800000008017c050000008015cc90000008005e710000008005ce90000008005ce10000008004e710000008004c40000000800100000000080008800000008000080
|7=>0x1008159cd00001002358cf00001002151c9000010001f8cf0000040489cc5000004044d0800000040445ec100000404140c50000040000a100000040000001000002120ecc00000018045e410000018045cc1000001804580000000180418400000018005cf10000018004cc100000180012000000010304d0100000103048400000010301c410000010301840000001030169100000103014510000010284cc1000001020bcd40000010201cd10000010201cc100000101c0ce000000101206110000010104de10000010101cd5
|8=>0x20004008400002000301cd100020001a4c800002000125cd10002000125cc9000200012588000020001258000002000121cd10002000121cc1000200012104000020001208400002000025c8100020000240000002000021cd900020000200400002000007cd10002000005ed10002000005cd10002000005cc100020000059810002000001cd900020000008800002000000800000200000004000020000000100001d0008504f000038180104d000038100504d000030189f0cc000022008fcc0000020089f484000020009f4c8
|9=>0x80002415c10008000045cc100080000409800008000005cc1000404040004000040004348a50004000425da10004000425d8100040004211c0000400042088000040004001c00004000025cc10004000005ce10004000005cc10004000005800000400000082000040000000c000040000000000002040044e41000201008ded10002010005ed10002010005cd100020100056110002010001ed10002008405cf10002008405cc100020084050400002008404980000200840084000020080254a100020080000400002000401840
|10=>0x8110220087cc04000000485cc5210022189fcc11800221087cc00402000485cd1020000002fec101002000bfcc401000010cfcc0008008100504d004c040005cc1004c04000100000420002008450040010021cc1004000022fc41004000022f44000400002256c100400002252400040000221a800040000221a400040000205ec9004000000101000400000000110020000101c80001000002f440000c00000008000080400010c00008000255cc90008000245dc100080002457c100080002454c1
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80000
|5,0=>0x100000000000202400040f000000000000000400000000001800000d0000000000000000000007800000000000000000000000201000042a00000000002c0000000000003000f80000018000000
|6,0=>0x38000000000001a002580c00810889c0000020001000001680041019489c000021000070c800000000010186752000000000000008105860b0000200148004100000573000000000693c0000000004a000a8001a00000008612000000000000102ac1028000000000002e0000044ae000018c08002580000040000000004084806000980006000000022002b8000e00
|6,1=>0x44001d001b43c273204400245f0001a00000002a000700000bc0200000000000000bf03a0400000005400911300022000d815aa0b378000005028000000000b4487502814001e0000000000000000000380000000012c00bd20000000056000006e4a80000003d80006000010000000217800110280000a6
|7,0=>0x5a80212d89e800001506c8400530000042fb003f9940006ac09a15600028cc40048800563580007082a844ac000aca4841147814011d7d01406d396a05860b9fa300e0a0000054ee3e4682a49a42791a00a2ac8b20b6f1dd732306ab82c48abac460058b2ace800000000000004be26e611958480d740ad689f001fa5c01000526ac2840440a22029e69e240a8028e5c
|7,1=>0x184220000078005d000543e15004142a650000196055780082930280048f8088a2035212802aac303988009a0004890000002e08a50009116007e854005e078c4a00002b51481142c1848009b11c12110035dac0001816149213ba538500305448112241c5c152f800ed1f0911408714a2dc2a00693d40600758022231028106400710442ad10fb24001171a38230b
|7,2=>0x18800a200000e606ed028001a8a0006859000885498005d8100072088000e2400465ed3a
|8,0=>0x675524edb8b8ce614c4dcd22124668723d511ac3140f43354deea853bfe786673ce132e05d0a68637ac8e45f5dad4ce82f17521952ec8c0e15adcad9a9e4731e4ca412868562a14d77a5e331bae4ed0e6c54a40fb4e51a7680e44b529bac80f8d944d998c08e11278b302b3972c967d4ba4b15b4683c385bec79b8816d148691aacaa59c55f92ca220d9e69
|9,0=>0x261710d3d0d2571c950f47e8733220fea179bc152f96343e1d26405089489
|10,0=>0x1d0edb65b
|11,0=>0x39
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 52 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_194 4 roots_194 ops++addP pm 2 dom_203 8 roots_203 ops++addP pm 3 dom_227 8 roots_227 ops++addP pm 4 dom_209 5 roots_209 ops++addP pm 5 dom_57 5 roots_57 ops++addP pm 6 dom_243 9 roots_243 ops++addP pm 7 dom_123 9 roots_123 ops++addP pm 8 dom_59 7 roots_59 ops++addP pm 9 dom_211 7 roots_211 ops++addP pm 10 dom_235 10 roots_235 ops++addP pm 11 dom_249 9 roots_249 ops++addP pm 12 dom_219 9 roots_219 ops++addP pm 13 dom_122 8 roots_122 ops++addP pm 14 dom_187 9 roots_187 ops++addP pm 15 dzo_210_1 5 roots_210 ops++addP pm 16 dzo_43_16 5 roots_43 ops++addP pm 17 dom_91 6 roots_91 ops++addP pm 18 dom_179 6 roots_179 ops++addP pm 19 dom_186 8 roots_186 ops++addP pm 20 dom_121 6 roots_121 ops++addP pm 21 dom_115 6 roots_115 ops++addP pm 22 dom_155 6 roots_155 ops++addP pm 23 dzo_171_16 6 roots_171 ops++addP pm 24 dzo_242_1 6 roots_242 ops++addP pm 25 dzo_170_16 5 roots_170 ops++addP pm 26 dom_154 5 roots_154 ops++addP pm 27 dom_185 6 roots_185 ops++addP pm 28 dom_241 6 roots_241 ops++addP pm 29 dzo_250_1 7 roots_250 ops++addP pm 30 dom_147 4 roots_147 ops++addP pm 31 dzo_234_16 6 roots_234 ops++addP pm 32 dzo_107_16 6 roots_107 ops++addP pm 33 dzo_218_1 6 roots_218 ops++addP pm 34 dzo_235_16 7 roots_235 ops++addP pm 35 dom_139 5 roots_139 ops++addP pm 36 dom_163 5 roots_163 ops++addP pm 37 dom_217 6 roots_217 ops++addP pm 38 dom_27 4 roots_27 ops++addP pm 39 dom_51 4 roots_51 ops++addP pm 40 dom_178 5 roots_178 ops++addP pm 41 dom_218 8 roots_218 ops++addP pm 42 dom_83 4 roots_83 ops++addP pm 43 dzo_106_16 5 roots_106 ops++addP pm 44 dom_42 4 roots_42 ops++addP pm 45 dom_242 8 roots_242 ops++addP pm 46 dom_248 8 roots_248 ops++addP pm 47 dom_184 5 roots_184 ops++addP pm 48 dom_120 5 roots_120 ops++addP pm 49 dzo_234_1 6 roots_234 ops++addP pm 50 dom_234 9 roots_234 ops++addP pm 51 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_210_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_242_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_170_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_250_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_234_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_218_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_235_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_234_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
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
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
def dzo_220_1:=0x22222222000000002222222200000000222222220000000022222222
def gzo_220_1:=0x22222222000000002222222000000000222222200000000022222200
def gsh_220_1:=0x11111111000000001111111000000000111111100000000011111100
theorem lowS_zo_220_1_196:Lower true dzo_220_1 roots_220 gzo_220_1 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_1) [(dom_220,1)] (by decide +kernel) (lower_slice_b (T:=gsh_220_1) [(0x11001100000000001100110000000000110011000000000011001100,0,8),(0x11110000000000001111000000000000111100000000000011110000,0,16)] (by decide +kernel) lowS_196)
def dzo_252_1:=0x2222222222222222222222222222222222222222222222222222222222222222
def gzo_252_1:=0x2222222222222222222222222222222022222222222222202222222222222200
def gsh_252_1:=0x1111111111111111111111111111111011111111111111101111111111111100
theorem lowS_zo_252_1_196:Lower true dzo_252_1 roots_252 gzo_252_1 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_1) [(dom_252,1)] (by decide +kernel) (lower_slice_b (T:=gsh_252_1) [(0x1100110011001100110011001100110011001100110011001100110011001100,0,8),(0x1111000011110000111100001111000011110000111100001111000011110000,0,16),(0x1111111100000000111111110000000011111111000000001111111100000000,0,32)] (by decide +kernel) lowS_196)
def dzo_244_1:=0x22002200220022002200220022002200220022002200220022002200220022
def gzo_244_1:=0x22002200220022002200220022002000220022002200200022002200220000
def gsh_244_1:=0x11001100110011001100110011001000110011001100100011001100110000
theorem lowS_zo_244_1_196:Lower true dzo_244_1 roots_244 gzo_244_1 6:=lower_iso_b (d1:=dom_244) (r1:=roots_244) (T1:=gsh_244_1) [(dom_244,1)] (by decide +kernel) (lower_slice_b (T:=gsh_244_1) [(0x11000000110000001100000011000000110000001100000011000000110000,0,16),(0x11001100000000001100110000000000110011000000000011001100000000,0,32)] (by decide +kernel) lowS_196)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(32,96),(32,160),(48,49),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,80),(64,96),(64,192),(65,69),(65,73),(65,81),(65,97),(65,193),(128,132),(128,136),(128,144),(128,160),(128,192),(129,133),(129,137),(129,145),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|5=>21
|6=>138
|7=>266
|8=>197
|9=>63
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xef313e1dbdd16b6cec8aa13ba922e06575a62a1c5d5ca48b7f478a144b69449b13c9bc30a1c2c0ee1a63e08570075ac02d4b003e0
|6,0=>0xcd7eacceb6ccd0cc8f95c8f2ec8cbcc8087c1aebbd99eb87d4b7bedac07aa87aea54a8a3ff0a3197a2e0b9ff1b9e12e949209135b8e46b8c9048baab887a5837908341482937816b5810c57f84a7e7f97b9097ab9577ebd75ebe75ba17513a71823708b2703786f4f86ec4e6e2e16d4886d41d6bf4269d596967866e89666cf637df6368a630cc61dee603615f5085920958c3458245573ec5499951d91510794eb744c408477594663b42eda40b88403e33f5c93f58a3f4c83dd3b3d8523b75a3affd3a426393303911e3760d35bab35b9c34b8b32ac031c6731610307852f4942b8562906225b5d24efe23c7223b901c4671bf081b4c31ab881a25a17d97158cd14f9d149a31329112eb212aae0fb5f0f76d0ccf00cc6f0b1bd0a78a09a130595c056c704fa70436c0369e03568032a102ef302878023da01fb00178200447
|6,1=>0xf4757ebb85e9aeee8c95dc0b7db164d7862d0883d082ecfda6
|7,0=>0x4a5dd4a4a849e914903848f764887a47fab47e3a475b8472f546ea945c09459fe4582643a57439bb4293641c5941201404744017b3fee33fcda3ea573e1bf3d7f73d3f83c02e3baa33a79d3a2333931438ca538a4b384bb380f1372b0372983664d357f433a6331d5930b732fcbe2faa72f4f52f2a32f0922ee652edf92ec1f2d8892d7302ca302c6e92a6522a0ac297f927f93273652723d26ca4264df2553a24f7124cd722b5722b0421552214c7209e51fd3a1f8511f4f41e5941e4511dff71dab51c9271bce91bccf1a54219b6418d2018b0a17baa1706616c0315876157b41503c1394b12784124b3112f3110a711020101310f7fe0f6800e8f90e6370e4030d5e90d16c0cbc60c7900bd260b2300b1220b10d09ca207a75076f306a71060d205b52057a40578404cf9049b30451604479038ca023e201c730158900eed
|7,1=>0xd6fdbcda56ccaafcb633c8deec833fc74e6c5711c381fc2282c1229bf7c4bed0dbe00dbd419bd2f4bbe1dbb9b8bab5fb8b84b7d2bb78a6b75ebb099dab8a8a8ee8a7bdca6fb3a38b1a295ea1faca1baba0c9aa09c1a07359d18999a5d971b596024933ff925a69240a91e80917879102790564900ee8ce968a8f78a8c58a153899a188858868f085cfc85c5c842a68346d80c1c7c9457ad52790f478cbb77e627441a7415c70a6c6f17e6e0e66c5786c3b56bff56b7c46b0c969e0f6910568fb668ccd6889f681d9678a36695564fa664ee5649b36408c63ea76394162cb76199360fb760e0d60d8660684603175fe795f8fc5edcd5eaaa5eaa35dfc55d2315cbde5ca425c9c75c9895ab275912e57d8e5748c567ca554235387d5343552837525dc523d3500e94fcdd4f0a44edeb4ebd44e8964e8664cffa4c6304ba4e4abf5
|7,2=>0xf8057f4511ea2f3e8527e636be5b65e0f69dd1edda627d7862
|8,0=>0x7fa827e3f47c6287b17a78f4d7850e76f8f74610743726e9b76e7286bb6f6b0e26ae4a68de368c7f664756598b6544764e5564b326378863189621ed61eb36182c6117b60bb05eb5b5c4405b5e75a6c859345571075657b56419558f854cea546d5542175321b523c251c0b4d5054d0d84c2a24b88749ff449e6d46c36464a44618342d85426ff424e03d3f43a5043a2413908438fb53874238544382cd3627d36194360ad35ad134c783440234100332ef332a73242a31909315b330b5d307653054d2ed412e0cf2d2762c3832b8402b56d2af7529bcd2920526d6825f812577d25128241ef22f3522bc120f9720afa1f4e91e9c61e8e81e8251e2541db151c2321ba411b75c19d43183a7180e514c08144771335c110040e6e80b7f80af6609fb2086950851b073ec07236053ff036ec02af802755025cc0173c0093e00245
|8,1=>0xfe3a6fad48f7a42f77b3f4418ef00cea8cbe9754e9524e8a70dcf47d7f9cd7abcd2b58d2574d1b38cf349cd636c35f6bcd19bb466ba5f3b963bb4ae6b2a30b173bb0571af72aad44eaaf1caad04aa8bbaa685a982ca8df0a32759f2239e9d79e2da9df8f9dc939db7e9cc8795d7495cfb9529f94af7943a292e84905fd8f7a48f738897f288b5c8863387c0287a828782986542863f38610a8561684d128393581df08158a81266811a5805a5
|9,0=>0xebf61e5286e1da2e1ae4dcc75bafbbb84dca8578a3bbca36c4a2a04916ab8d2fb8cf2d860bc8562f8310d7e5b87c6cd790a87570c710486f4446578e62ed661f5461737610fb5f6015f3695cd1f5971f535d152861506e44aa9a49f644981f46b31452724154f3c748381b035f8635ac333051323db2cb1629eea29dfc2780e26145252ec201c21abe0186c818196152a613b71131de0b09008711059bd
|10,0=>0xed820c6eb1887d379b4e7762c470633920c0b254
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0003333333333333333000000000000000033333333333333330000000000000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333000033330000333300003333000033330000333300003333000033330000cccccccccccccccccccccccccccccccc8888888888888888888888888888888b33333333333303033333333333330303333333333333030333333333333303000000000000000000000000000000000cccccccccccccccccccccccccccc0003333333333333333333333333333333333333333000000003333333300000000ccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c2222222222222222222222222222222222222222222222222222222222222222cccccccccccccccccccccccccccc0000cccccccccccccccccccccccccccc0003333333333333333333333333333333333333333333300003333333333330000ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c3300330033003300330033003300330033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333333333333333333333333333333333333333333332222222222222222
|0,1=>0xcccccccccccccccc0000000000000000ccccccccc0c0c0c00000000000000000000000000000000333333333333333333333333303030300c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c0c0c0c0c0c0c0c0c0c00003030303030303030303030303030303030303030000000003030303000000008c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c888888888888888b333333333333333333333330000000033333333333333333333333300000000ccccccccccccccccccccccccc0c0c0c0ccccccccccccccccccccccccc0c0c0c03030303030303030303030303030303030303030303030303030303030300000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c0c0003333333333333333333333333333333333333333333333330000000000000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccc000000033333333333333333333333333333333303030303030303030303030303030300000000000000000cccccccccccccccc0000000000000000c0c0c0c0c0c0c0c3333333333333333222222222222222233333333333333332222222222222222ccccccccccccccccccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c3333333333333333333333333333333300000000000000000000000000000000
|0,2=>0xcccccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc033333333333333333333333333333333330033003300330033003300330033000000000000000000cccccccccccccccc0000000000000000cccccccc000000000330033002300230033003300230023003300330023002300330033002200220c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0c0c0c0c0c0c0c0c0000000303030303030303030303030303030303333333333333333333333333333303000000000000000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0003333333333333333333333333333333333333333303030303333333330303030cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0003030303030303030303030303030303030303030303030303030303030300000ccccccccccccccccccccccccccccccccccccccccccccc0c0ccccccccccccc0c00000000000000000000000000000000333333333333333330303030303030300000000000000000cccccccccccccccc0000000000000000888888888888888b333333333333333333333333333333333333333333333333333333330303030ccccccccccccccccccccccccccccc0c0ccccccccccccccccccccccccccccc0c0000000000000000000000000000000033333333333333333333333333333030
|0,3=>0xccccccccccccccccccccccccccccccccccccccccccccccccccc0ccc0ccc0ccc33333333232323233333333323232323333333332323232333333333222222220c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080808080808080b3303330333033303330333033303330333033303330333033303330333033300000000000000000cccccccccccccccc0000000000000000cccccccccccc0003333333333333333030303030303030333333333333333330303030303030000ccccccccccccccccccccccccccccccccccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0303030303030303030303030303030303030303030303030300030003000300cccccccc00000000cccccccc00000000ccccccccccccccccccccccccc0c0c0c00000000000000003333333333333333000000000000000033303330333033300000000000000000cccccccccccccccc0000000000000000ccccccccccccc0c3333333333333333333033303330333033333333333333333330333033303330cccccccccccc0000cccccccccccccccccccccccccccc0000ccccccccccccc0c33333333333333333333333322222222333333333333333333333333222222220c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000033333333333333333330333033303330
|0,4=>0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000033003300330033003300330033003300330033003300330033003300220022cccccccccccccccccccccccccccccccccc88cc88cc88cc88cc88cc88cc88cc8b3333333333333333333333333333333030303030303030303030303000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c000c000c000c000c000c000c03030303030303030303030303030303033333333333333333333333330303030000000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c00000003333333333333333333333333333333333333333333333333333333322222222000000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000000000000000000000033333333333333333333333300000000c0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccc0c00000000000000000000000000000000333333333030303033333333303030300000000000000000ccccccccc0c0c0c00000000000000000ccccccccc0c0c0c000000000000000000000000000000003333333333333333222222222222222200000000000000000000000000000000ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc3333333333333333333333333333333333333333333333333300330033003300
|0,5=>0xcccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c000c000c000c00303030303030303030003000300030003030303030303030300030003000300ccccccccccccccccccccccccccccccccccccccccccccccccc8c8c8c8c8c8c8c8000333300003333000033330000333300003333000033330000323200003232000000000000cccc000000000000cccc000000000000c0c0000000000000c0c3333333300003333333333330000333333333333000030303333333300003030cccccccccccc0c0ccccccccccccc0c0ccccccccccccc0c0ccccccccccccc0003323332333233323332333233323332333233323332333233322332233223322cccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc00000000000000000003333000000000000333300000000000033330000000000000000888888888888cccc888888888888cccc888888888888cccc8888888888888888000000000000000000000000000000000000000000000003333333330303030cccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc00000003300330033003300333333333333333333003300330033003330333033303330ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0c3333333333333333333333333333333300000000000000003333333330303030
|0,6=>0xc0c0c0c0c0c0c0c00000000000000000c000c000c000c0303030303030303033333333333333333030303030303030333333333030303000000000000000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c00000003333333333333333333333333333333333333333333333333322332233223322000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000333333333333333300000000000000003300330033003300c0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0ccc0ccc0ccc0ccc000000003333333300000000333333330000000033333333000000000000000088888888cccccccc88888888cccccccc88888888cccccccc8888888888888888000000000000000000000000000000033333333333333333300330033003300cccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c000000033033303330333033303330333033303330333033303330333003300330033000000000000000000ccc0ccc0ccc0ccc00000000000000000ccc0ccc0ccc0ccc333333333333333333333333333333330000000000000000333033303330333000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000000002233223322332233223322332233223322332233223322332222222222222222
|0,7=>0x33333333000000003030303000000000333333330000000030303030cccccccccccccccccc88cc88cc88cc88cccccccccccccccccc88cc88cc88cc8b33333333333333332323232323232323333333333333333323232323232323200cc00cc00cc00cc00c000c000c000c000cc00cc00cc00cc00c000c000c000c2233223322332233223222322232223222332233223322332232223222322232
|_,_=>0
def sP:Nat→Nat
|0=>0x5879e3e080861e78d02020020f340809b1e0831d3858284060838b143c402264850434088860a10682026c50434080801e64a8228482830448b901e2010030382830418b960a10a8202005051008a12083c18226485041a089920a101822218505100838b14244020e182840608080
|1=>0x1e201010c387992a0809220146820218b961e681010ca48051e2011402485041a08a121c3cc9a04040101ea01070c5828f1a09312209479a041c3101e78a8202187193420602284850f3409206202820d040518e1e88f82021880f0608992208078d040458e083cd0228049051e20101
|2=>0x40458f100809b1c2938d041c3101e0c106523880d18c17ae02485051008386201078d042cc0e143d68228187041e0c11424385043408386203d41f041c3101a3009b583880f0418bab1c4028f2a080802010783040518e4210682281870f327c1010c4079e040458e0a34101245c82a
|3=>0x83c1010cacb041e68111021850f3408886209c79a04040104e3c6820e503051e34101364079e0608a061ccc78d0404910326840c04040271e0c1070c4050f3408080200c40c044c90a08341130c3908f100808b1c8478804043161ec810126488041e6810728182841a080803e6840c
|4=>0xc382830418b8e2010799040458e083cc820218b041e0c1110c3868c60bc1010028788041c58e143c4020e18b0f2a20107281828f1a092011610783040400e1e68106305880f446810124405041a088861c10783044c30e1e654020218b0f320c1140c5820f04045ab1c2820d040400e
|5=>0x343460202007833e080922024783041c3101a318020ce070f6e0808b1c3cf1a04049101a3183604043351e681010c4079e340808b1c3cf1a04043160a10682021988a1e541070c4078804049920a106820e045a82a346020e2d2851a08092209428d040431614246820e1880f3254114
|6=>0x28488051e0c1140c5820f34080801e0c106743880a0a3411424405051a08a062c14203040458e0a101820218b0508341010058783042ce8e2078f8d18080861e0c1063a5880a1e20114243868c72bd701003ca820e5030f34080922e4079a04043172c28788040518e0654d0c045091e
|7=>0x1a088810c3cc9a04509101eecd02280430f32681140c5879e10080861c3463c5e49c104a3c6820e18b0a1e3412416382842a080862c1420d041ca060a101820e188041e641140c3853b3408086203ca9a04500921e0c106303880f1a080181c407993c0808b1c3cc9e04043160a3c182
|8=>0x2818b0f320c1010c588371a30101163850f100808b1c78d0d180809220287a8045030e2078d0d180808b1c3c10124707103c6868c040431634206020200b0f7c0809b1c405043408092202821a040458e1410d020218b041e681010cc4d08180809b1e34106303881a103010100f4284
|9=>0x1a31a2f04503161a31caf5c0458e143c6822618710447868c040430e1a31caf5c04316065440c045030e3420602280490f44080861c4068c78b83381c4019f1a30101244028f1a08080203c4020218e8e203cd020e503101410d0202187101e64182022c7101ea0f8202187103234602
|10=>0x143c68202007101a320af024880f44541010c3880f040432b2c4079a044408620346365e08086205468c041ca06083c6820e5030e1a317ae020068c68bc11424405271a080861c4068c6c08092203463072080861c0ca8c041c3101a31caf5c04910083c682024c30e083c1820e18710
|11=>0x1a301010c4020f1a088810c387b204500921c4050f1a088861c4138f1a080801c4028f1a093061c4100f1a080861c4018818080a31c2828d0404910326840c045030e1e0c1130c388431030101163820f3408a010c3850f3408a061c4079a0406110083ca820218b0e1e544020e04310
|12=>0x68c010116387c6041c086203463460080862c1079a0404910083cd02022c7051a080862e388041e681010c593851e341012440783040400e203cc95040430e209c78d04500861d1478d040430e203e2020e18710062060228487051e2011402187271e0c1010c3880f50083861c40f95
|13=>0x320c40c0404316327868c040458e1e341010d1c710327868c04043161e64101163880f32080862c40788040430e627818818080861c3c6820c60b0e203c4020e0458e0a3c182024880f06088861c4068c7300101163879e040430e203c4020e04316123c402021870f1a093061c4068c
|14=>0x41c08b20287c6040430e203e50202187102a6868c04500921e54402280430e1e08086923880f90080802c3880d18c17ae021870d18fd80202187091e3410702188032a68602024881a1a301013640f8d1808092206840c041ca06320c40c040458e067c68c041c310083c6820c60710
|15=>0x1e201010c5870d18bc092964040c04045ab1c2060202195963420602220430d1934124022c70f040434c1c40f9a10301010c4068c5e0434b2c3463c5e061101a31a2f04040101a31e02482c7051e341010cc480a1e2010124388041e341014638795041c086202878804043161c1478d
|16=>0xd3c710663c68202187101414682022c7103434602480458a0a341010c588282a34602022c70310301130c387a250080861c4108f10080861c4078804040161c2848d040430e208428f1a08092203ca88040458e14146820e1880d180404e2c3880f1a0808b3a3880f1a080863a58827
|17=>0xc3880d18c2002021870d18d9702022c7511e341010c388051e0c1070c4068c6cb81010c587990608a061c4068c72083381c4078d040433a1c4079934080922010782021958e2028788045030e0620602020070f1008a0124391081a30101163850f2a080861c407d0040430e203c101
|18=>0x418e8e201478d04500862c3463978bc092203d11a040430e2034630780808b1c14783040458e203463978bc0862c1478304043162064d0d1808a12203ca8202007100620602221870d18d9702024881934346022818b1e103460202187051e3410100588091e0c1010c3880f32a0101
|19=>0x1a31e400ce0710506840c040458e506840c04043161e6810100421881808a061c3c6820218c0e2054d0d18083940c3465204049100634602482c70d18e5e020e18b0d18f1794244068c5eb80802c1478d0450092206440c040458e1a31e2f2818b1910301010c594031a301070c58783
|20=>0x218b10327868c045030e1e0cf8202187101edc1010c3880d18fc106703880f3c681010c3880fa6080861c4078d0404d8e20f868c0404d8e203463460b80861c346346008a061c1420d041c086203c402024c30e505468c041c3104a146820218710083cc820218710506840c0404910
|21=>0xc4019a1808a12203c68203547101f501010c3880d18f1781004138f1a083181c4019a1808a062c3c682480458e423c1820e18710326868c04040101a31e020ce07101a317820249c10423c682022c710423c6820218b100654d0c045030e1e64d02022c710320c40c045030e1e64d02
|22=>0x1c401ad1808a061c346395e049101a3183c5c0430e1a3183c045030e143c68203087101a31caf0218b05083410116382841a080862c2878d041c58e202878d041c31620a0f9a1808086203463c80bc092203eb820218710141468228187100a10182021871034206020200c9f1a30101
|23=>0x16388251e341070c3881a10301010cc468c68e41010c587da040430e203d103040430e203c6820c6071032a068c0404316b23c68202187101e0c101843880f1a083940c5868c7ebc1012440783041c58e203c1820e18b106434602024c9101a31c820e18b1910301140c3868cb00809b
|24=>0x1904101243880f32083810c3881a1a30101004078d040435b1c4068c040435f1c4068c5c080801c346345c0430e2034634045030e203462e021af0e20346395c080921c4068c60bc1010c3880f340808b1c401881808a061c9c78d049830e203410117707101e64d0228187101f0c101
|25=>0xc3880d18f1701163a98d18080861c4068cc4080861c4040d18083940c394081a301011638799040430e203c682028c7101034602024c30e06206020e187101a3010100f47101ec8101243880d18080e01c4068c80b8101163820f1a080921c4020f1a080862c3868c7eb81010c3880d
|26=>0x18d81010c388081a30111021870d18e57ae02187101a31fb9040430e201478d041c0862064d0d180808b1c40d081808a010c38c9a1a301010c588033e3460202187101a332020218710323460228187106e346020218710143c40202187101a30101363881e343460202187101eb4101
|27=>0x203463c041c316203c402280430e3420602022c71534346020e0431034206020218b0d18080e71c4068c79980861c4068c82bc0861c4078d040431d1c411191a301010c388033430101244068c5e080802c4068c78bc08b1c4068c78bc0862c4068c04043651c4068c68bc1140c3880d
|28=>0x203464004043381c40788040458e34346020e045904e1478d040430e2034602024a58e2034602021a5961c3463c040610e203462f04500922034641041c30e203464d041c08b1c405051a080861c4218818080861c4068c049008b1c3462f04500862d5068c040430e203463c041c58e
|29=>0x38819062060202187103e346020218710327868c040430e20a018d18080862c3868c68f0101163880d18d1e020218b104e3c68202187101034602028c70d19a41010c3880f10083810c3880d18e600202187100a3c18202187101a31a30040430e201079a040430e206868c0404331
|30=>0x1c4019a18080862c4068cd6080861c4068c7ef01010c3880d18f01240c3880d180808b7a3881a1a30101005880d18083940c5818d18080c21c4028f1a08092200c68c041c58e200c68c041c3162054d0d1808a010c3878d040430eac414031a3010124388032a6860202187101e34101
|31=>0x80080861c4108f1a080861c4079934080861c40783040458e208840d18080861c414151a301010c3882206346020218710343460228049102a6868c04049101e544020218710421478d040430e206868c04500862c20602021958e200cd0c040458e208478d041c0861c4050f1a0808b
|32=>0x203463c5e5030e206440c040430e20a018d18083861c4028f1a08a010c388281a301010c587035a301010c3880d18e5e2f02187101a3183c040430e21b868c040430e203c4020218b0e1a301010db47101a336020200b0e2064d0d1808a061c4218d180808b1c4068c5e080c2203463f
|33=>0x1a31e0222187101a3010124707101e541010c38828342060202187101a31e0202007101e341010c398901a301010c70b0e1e34107022c7101e341070218b10123c68202187101a31cbc041c30e200c68c049030e2034652040430e20a068c040490e203568c04500861c346020219c0e
|34=>0x18bc1010ce07101e3410100587101e0c1070c388271e341010c58710445468c040430e2034640040400e2034634040458e20346340404316203463c800430e202878d04043161c4110d18080861c4068c5eb808b1c3d403040430e20346345e08092202878d041c30e203462f5c04316
|35=>0xc707100a1068202187102a346020e0431090346020200b0e20346345e080862c4068c79017810c3880d1808086de3880f86080861c4018d18088861c4078d04900861c4018d18080801c4068c7e080861c4220d18083861c4190d1808a01243880f06080862c3880d180ae81163880d
|36=>0x2c3a30d18080861c4068c78bc0861c40c9a1a301010c388031a30101163880d190178202187101a31a39040430e200ca8c040430e205468c040400e203c682220430e206540d18080861c4079504043161c4280d18080861c4068c040780e2034602021a78e203c6820e5030e203c101
|37=>0x19cc101243880d19001010c587101a31cbc040430e2034602e40490e20a018d18080861c4068c5e0809220346020218731205468c040430e206868c041c08620346020e0458e20346020e04316203463c04043161c4068c78083861c4068c040434b1c4040d18080921c4040d1808086
|38=>0x863460202187101a317820218b103434602024880f10080861c4068c040430ec240783040430e203462f04500861c4068c04900861c40d0818080861c4019a18080861c4050f1a080861c4068c04043711c4018d18080862c3880d18080802c388031a301070c3880d1808086e83880d
|39=>0x2c7101a30101843880d18088810c3880d18e41010c3881a1a3011402187102a6868c040430e205468c04043161c4068c041ca061c4068c68083810c388051e341010c3880f1a083810c3880d180808638388281a3011402187101a333020218710503460202187101a31782022c710
|40=>0x1a080861c40d0d18080861c4068c04043161c4068c5e080861c4068c040458e20346020e0430e203460202007101a3208202187101a31e02022c7101e341010c587101a3200202187101a317ae02187101a31a2f040430e20c868c040490e20346020218768203c682022c7101a30101
|41=>0x1a301010c388031a301010c3880d18f01010c3880f
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x786039301b180ccc060602d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x118b88a9c446e21c710ab8839c40ee20070fcb87c9c3d6e1e470eeb8759c39ee1c870e0b86e9c366e1ad60d33867dc330e19170c53861182fae17760b8385a5c2c4e15b70aa38535c28ce13f709c384c5c254e123708e38455c21ce1086080b83e9c1e6e0ec7072b8379c1aee0d070653030dc178e0b570573829dc140e0997049b0231c10ae07e7
|6,1=>0x1f6b8f99c7bee3d871e8b8f29c786e3bc71dab8eb9c74ee3a071ccb8e49c716e38471beb8dd9c6e0c36971b138d6dc6a8e34d71a338cfdc670e331719538c8dc63ac3167187b8c21c602e2fa7179b8bb1c5cae2df616c38b45c594e2c3715e38ad5c55ce2a86150b8a69c526e28c7142b89f9c4eee2707134b8989c4b6e2547126b8919c47ee2387
|6,2=>0x864e42b721239075c82ce4106204b9009c7f6e3f47
|7,0=>0x30cb98460c13060272fd417ca0bd505e282ed4174a0b9505c372de396d20b5ae5a672cf4165a0b20c58882c0415e20ae2e56982b13956dcaa7054c72a2414f98a6d052e8293b947e0a30e51082844140209f104f082744138209b104d08264b9309c97504b28255b928e0938e49482464121208fae47582373919dc8bf04578227c1121c88104397
|7,1=>0x3fcc1fc9cfd6e7e473eeb9f560f9ce7c683dfb9ee1cf6107a973d0c1e660f24e78b73c1c1dee0ee7076c73b241d720eaae74d83a2c1cf60e6b072d839339c7dce30e710838441c020df106f0837441b820db2e6d27365b9b0e0d7706b47356b9a99cd3d0697734839a25cd04e67a8339b99ae0cc8e65d732ac1939cc8d063f731bc18be0c4f06207
|7,2=>0x4f13276dd3a709cb84e23a6f5d36b09ae74d3ba67e1330e99174c53a60a12f6e97384b5c258e12b7095384a5c250e127709347496ba496123b09158486c241611fb08f58476c239611bce8d684674231a117d08b77457c22a1d142e89a74494222a1106e87c743a421b210cae85d842ac2139d08d083e841bba0be104f0820740cba046101308018
|7,3=>0x5e442f021772ebb275d542e8dd738eb9485c6bae19d6fd0b7775b83ada216c10b5885a8bad29d686eb3b8599c2cae16470b1c758a42c32160ccafe857bbabc1d5d2eae2756d42b4dd598eac4855e42ad215590aa4854e42a5215190a84853e429d214d90a65752ec2956149cea47751fc28de145f0a2785103a86214210a088500427e213e109e88
|7,4=>0x18270c0c760242ff5d7eb0bee75f342f7dd7af0bd07
|8,0=>0x707c381e1bff0df786f83b7a5dbc12dd976e93b72a1b850dba86d8cb6a9db450d9a86c94362a1b032d7986b8c35a25abf2d5786a74b51a1a7b2d349696434921a390d148686bb41259faecf676774339a19bd0cd68667bb321d9810cb88658432a5d944ec9a86494322a19032c798638c31a9d8c50c5a8629bb12e18870c3b86194b0a65844ec1b7
|8,1=>0x80dcc04a6015100377fd4bfca1fd50fe377ed4bf465f912fc087dc43ec21f4f2f9f87cbc3e3e1f0d2f7e87bb43dba1ecb2f5d87aac3d361e8cef3e879bbbcbe1e4f0f1e978b43c365e092efd777a4bbb21dc72eda9768cbb225d810eb97758c3aa61d412e988747cba1e1cff0e769738339a21cbf2e578727c391e1c7f0e3787174b89a1c3d0e177
|8,2=>0x9114486a2426f20b8901c47f1e3e911ec88f1cc76a63a331c988e13c6ea236511aa88d14466a2323318988c0c45e262e1116978b04c55e629f1147889fc44de225d3126888fbc45e221f110788803c3e221e110e978704c36221a110c88860442e2216110a7984fc425e211f1087883fc41de20df1066982ecc156209b1044981dcc0ce2058f0248
|8,3=>0x124b9921c48ee2467122a9
|9,0=>0x5131e889143c8a1a450b22849141b9a09c502e2808f3fc89fabcfb627cb13dc99e9ccf2a678513b999d8c4ea62743139899c844e222701137889b844da5e6c4f35a89a9bcd2a6685133a899944caa264513199988c4c26260312f989784cb9e65bf12d69967bcb1e257f12b78957c4a9e253d3296894744a1a24fd127689374499664bb12549
|10,0=>0xa44c520628f4f4728a354518a28b6f4538
|11,0=>0x14917
|_,_=>0
def wAt:=mkWire dB 117 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1a310c391e411e051a31244134050c391a391a311c411a3102391a5102414e040a4114411e051a31024134051a390c390e4302391a051a31283b0c39024142430c411a390c391e4102411a311e390c591c411a311a312839024134050c3934411a391a311e411e391a310c591a5920391a310e4102391e051a410c411e391a31
|1=>0x1a050c411a411e1d02391a310a051e391a311a491a31283b02411a310c591c411e411e391a310cc51a31025a1a411c410a411e391a311a411e391e051a314e0708391e051a31103b0c391e4102411a311a31503b1e391a310c591a592039163b0c4114391e051a310c411a3132431a1d023934050c3934411a391a310c390241
|2=>0x1a391a311a311a31283902410c5968431a410c411e0502391a311c41023910391a411a310c410e430c59203928390241283b02411a31063906411a051c4106391a051a3134071e411a3102591c41283902411a311e5920391a310cc5025a0c3934050c5920391a391a410a411e391a310c5920391a391a310c39283b02411a41
|3=>0x1a311a3120391a311a051e411e391a310c591c411e411e391a3102410c391e051a315c0516390c41044104391a311a5902411c4102391a311a411a31163b0c410c3934411a3902410c5932430a431a311a910e430c4102391a591c411a411a31283b0c3902411a31100510391a410c4114411e051a3108051e411a3134053441
|4=>0x1a390c591c411a411a390cc5025a1c410c391e051e411a391a310c411c41025a1c411a410cc5025a1a3920390c591c411a411a3902591c41024134050c391a391a3134051a3902411a3114411e051a310e430c411a591c411e411e391a311a311a311a3102410c3934411a391a31324302410c391a311a310c591c411e411a39
|5=>0xe4102391a315c3904410c39503b06410c591c411e391a310a071e391a411a3102411a3902391a311e051e411a391a310c4106391a051a311a31503b1a5102411c4102411a1d0239203906391a051a311a910e430c4102391e050c411a411a3132430c3934051a511e0502411a310c41324334051a3110071a410c3932433405
|6=>0x2411c41023902391a3116390c41044104390c395e05043902411e591c411a31723b04510c3902417e43723904510241344102391a391a055c050c3904390441283b02411e4102391a051a315e05043902415c050c4104410439283b0241324132431a1d02391c415c0504410439103902411a411a051a391a410c3902411a45
|7=>0x1e1d02391a051a41163b0c410c391e391e051a31024134051a391a311a05283b02410c41063b1a411a051a391e4102411a311a391e0502411a311a391a3124430c391e411a311a591c41023910391a411a310c591c411a3104390c39784304051a311a591c41340720391a391a311a39283902411a317e3b80055e4104391a59
|8=>0x8071e411a311c411e411a391a310c390a411e391a311a051a3116390c41340534411a391a311e5920391a317605083b1e41064302391a051a311a051a410c39024102411e391a411a310a411e391a051a311a3102391a510241443b2a051a5920392839024102411a311a490c390e4102390c591e591a314e040a411a314243
|9=>0x2391a311a31025a1a411c41324306391a054e071e591c411a3102390c411a411a310c391e391a051a311a050e4102391a315c390c415c0504411a3132431a1d02391a411c4102391a310a431e391a411a314e040a411e391a316843041d0c41023902391a3134431a396843783904051e410c391a391a310c411e411a391a31
|10=>0x1a3134531a3902411a311a311a010c591c4168435e05043968436841041d02390a431e391a311a0534411a390c390cc5025a1a3920390c39503b1a51024102391a411a39024106391a411a050c41503b06411a054e0708391a31063920391a050c4132431a1d02390a531e39024132431a1d02391a311a1d0c4102391a1d1c41
|11=>0x1a390e430c4102391a31564134071a39503b10051a4104395c0704411c410405043924430c395e05043924410c390c4104050e430239025a20391a410c391e051a311e411a31163b0c411a591c4102391a311e051c411a411a310c411e3902391a311e051a3134431a398c051a3134431a39024134411a390c39024110391a41
|12=>0x2039100510391a410c41283b02411a411a051a311a5102411a411e1d02391a310c591c411a411a310a431e391a310a050c391e391a310c4110391a411a311e391e0502391a31900b1a010c591c410c410a071e391a310a071e391a311c411a411a315c070c39043904411a4134071a390c41340720391a391a4102591c411a41
|13=>0x439723b0c415c051a051e3902391a31723b5c050441063902411a051a317e077239045102412e3908071e411a3134050c391a391a3134071e411a391a311a411e0502411a311a411a0516390c411a311a410c3902411a410c411a311a591c411a318641063b1a052a071a311a591c410c411e391e051a310e431a390c410239
|14=>0x1c4106411a050a071e391a051a3102411a31043978410c390405684378390c410c411e391a051a3178411c4104051c411e391a051a310c39024134051a391a310c591a591c41283902411a411a05723b5c050c3934051a3902414443503910051a411e391a310c5920390a431e391a051a311a31063906411a0568435e055e41
|15=>0x10051a391a410c3904591c4110051a411a390c4110051c411a411a391a391a3124410c390241063b1a411a054e070a411e391a31024134411a390c39044d283b02410c411a050e4302391c4178410405040504390c3902410c590441043920390c391e3902411a311a411a1d0c410239043902411c410405340520391a391a41
|16=>0x2410c411a3134051a39063902411a411a051c411a3134051a3932431a1d0239503b06411a051a311a311a910e4302397e0778591c41040532431a3134051a391a311ac5025a1c410cc5025a1c411a310cc5025a1c4168435e05043968435e0504391a31283b1a4102411a31100510391a4102391e5102411a3134051a391a31
|17=>0x1a311e411e391a051a310c591c411a411a39503b064106391a050c3902411a391a050d591e5a1c411a311a31065b1a051c410405043924410c394e070a411e391a311a051c411a3902411a310e430c41023902391a0534051a3924410c397e0778591c4104050c3980075e4104390c411e1d02391a311e1d02391a3134411a39
|18=>0x1a051a311a051c4102391a31283b1a490c390241045102411c4102391a4102411a1d02390cc5025a1c41103b02411a411a055c050c390439044178390405783904051a3124430c39043978411c4104050c411e411e391a311c411e411e391a310c411e0502391a311c41503b1a5102410c3904055e4104391b591e5a1c411a31
|19=>0x43904415c0504410c3968435e0504391a311a390c4102411a411a054e0419760e2d0c41023902411a3134051a39063b0c411a051a3114411e051a311a41025a1a39203978417839203904051b6d1e5202411a314e070a411e391a311c41063906411a05025a1c411a051a3124430c3902411c4102391a3104390c390c410239
|20=>0x2411a4102390c4110051a411a311a1d02391a31163b0c411a41283b024102391a411a05020216390c411a311a490c390d85045a1c410c415c3904410c391e411a3120391e411a3180055c3904410c39784304051a1d02391a311a3924410c391e5202411a31bc415e070439044116390c415e05043904415e05043902415e07
|21=>0x20390405383910071a415e0504390241723b045102410e411a4102395c0504410439045102411e3902391a310c4134051a391a411a3902411c4134051a39503b06411a0504c5025a1c4102411a1d02391a910e4302391a411e051a310cc5025a1c41324334051a391a31103b1a410c41044104051ac5025a1c41c641783b0405
|22=>0x241023978430405042d0c4102391e391e051a31063b1a411a050e430c410239024104392039065b1a051c4104050c4102390239203904051a4102411a311a411a390c41023934411a391c411a411a390da11a5a1c415e43043904057843043904050a071e391a311a1d02391a391a050c390c59043920390c41043904050439
|23=>0x1a51024132431a1d023906411a051c4178390c4104057839203904050a411e391a311a41163b0c41d4055c3b04411a4102391a315c055c3904411e391a051a316843041d02391e411a391a31025a1a392039800704591c410c411a411a311a390c4102390a411e391a310c395c0704415c0704411c41040524430c3904390c39
|24=>0x34071a391a411a391a050c411e1d02391a310c411e051a311c411a391a05785b1c41040578591c41040504050e430239020216390c411a390c59203902411c41023924431a050c390c391e391a311a050c41023902391a05203934411a3902411e5a1c411a3106411a050c3934411a391a051a3116390c4106391a411a05503b
|25=>0x103b1a417841043904056843783904055a05103b1a411c411a411a31101f1a41023904010c591c41024134051a39063b1a050c41043924430c3904591c411e1d02391a311a3134051a390c411a051a31503910051a41103910051a4106591a051c411a390c39024134411a390c3910391a411a310a051e391a311c411a390241
|26=>0x2591c41040510071a410c391a311a591c411a3910051a41040516390c41025a1c411a3110071a411c411a310c4102391c4102391a310a431e391a317841040502391a050e430239044d283b02411a510c3902410241103b1a41800704591c410241043904051a411a1d0239023906411a051e3902411a311c411a5102411a05
|27=>0x16390c4178591c41040506431a0502391a490c3902411c411a051a310e2d0c41023980075e4104391a310c591c4102391a051a311e591c411a311a591c410c5904591c41041d0c41023978392039040504591c4104051c411e051a3150391a5102410c410441043906411a051a310c395e0504391e0502391a31044104392039
|28=>0xc415e4104397839784104051a051a591c410c591a591c410e4102391a31063906411a051a311a591c418641063b1a050dc5041e02392a071a591c41024102391a3110071a411a311e411e391a3102391a5920391a010c591c415e050439203904055e4104395c1f04410239063b1a051a3102591a051c410e4302391a311a05
|29=>0x1a31045a1c411a051a31043902410e4302391a411a391a391a051e051a31041e02391a051c410c591c411a0502391a1e023904490c3904591c417841040502490c3906411a0504390c39025a1c411a591c411a3902390c4102391c4102391c410405040502395c0704411a410c391a411c4134431a390439040534051a391a05
|30=>0x1a391c4104390c41023916390c41784304050c4104051c411a3104591c41044104395e0504391a490c391a5a1c410c411a3116390c4124430c390e410239045102411a39024134411a391a591c4102410239041d02391e391a3102391a3110071a411a5102415e4304391a51024104390c41063b1a05043920391a390c391a41
|31=>0x1a0504051a31
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x151000004c8000000001ca00000000000010c01c4000000000a400140000000
|6,0=>0x5410a62144827900000000136626484b90961126624480000901116a220c42207f500001e943b987340e421b5400006850ca6000000006140be4170c2c205710ac20000000051509e4130c000047500000000212800000000fcc1da0365062a0bc81618000050809880000000042a07c80d28164
|6,1=>0x46d000000002306458888a910121e24384000109500000000000108120a641047fa80001fc23f080000f841e6a000000000001de83a9472a80001c8238106e20da2000036440000d45000000000000000000000006910cd5198232106298c2300002f900000bd117822e885c10b3516422b905610aa2
|6,2=>0x9c1933526424c4497912a50000499092111f5
|7,0=>0x43e886d10ba213441e8834904a20724086804cff19fa43ec87cccf7a1eb43ce878d0efa1db43ae8750ce821cd339287150e0a1bd437646dd0d9a1b0335886a10d221a0433c46690cb9993432246350c4a185430285f50bd917832e885c10b6216842c885810ae215842a885410a69949428c650909f993b4
|7,1=>0x61e6c2d183a30345fe8bf0d7c22f535e28bb5174a2e545c64b7d16da2d745a68b3d165a2c745868afd15da2b745686ac11569aa9454a8a8514ea299452c6a4cd481a8c45126a18d41227e44f489dcd39a26f44d6899d131a25f44b6895d129a24f44968920d222240447a68e511aa231445a88a8d139a234
|7,2=>0x7dc8fa91f323e337be8f6d1ec1bd447a08f311e423c447808ef4ddca3b7276680001d81bac47526e951d0a39d47328e58dc99b8f47168e1d1c1a37f46f860001bc237536e28db51b4a36546c28d751aca35546a64d40da6234840000d111a0233f16768cdd19a1b3046588ca4d92a321463a8c6518aa3123
|7,3=>0x99c9330a6424c4498452f925d24b6496492b92559ca749469284a4f949c39309251248248c49163220e42248048fe31ed23ba47348de91ad233a46348be916d22ba45528a29135224a445488470fce1da437486690c0e1624284848908120e2418482a7048e079c0e181490192019c0037f88fe89fb23f24
|7,4=>0x2788ced49d293952711cde49b4935900004d24
|8,0=>0xb5a76a8ed39da43b427678ecd9d983b2a7648ec79d8c3b14561cec21d813afc75ecebc1d753ae475bceb6956a3ace7590eb09d5e3ab67560eaa9d523a9e7530ea49d463a867500e9e9d3a3a6e74d0e989d2e3a5674a0e929d223a3e7470e8c9d163a267440e869d0a3a0e7410e809cfe39f673e0e7a9cf23
|8,1=>0xcd879a4f331e633cc25978f2d9e583caa7948f279e4c3c927918f219e403c7a78e8f1b9e343c6278b8f159e283c4a7888f0f9e1c3c327858f099e103c1a7828f039e043c0277f8efd9df83bea77c8ef79dec3bd27798ef19de03bba7768eeb9dd43ba27738ee59dc83b8a7708edf9dbc3b7276d8ed99db03
|8,2=>0xe567ca0f929f223e3e7c70f8c9f163e267c40f869f0a3e0e7c10f809efe3df67be0f7a9ef23dde7bb0f749ee63dc67b84b6f1edb3db07b54f691ecf3d987b24f631ec33d807af4f5d1eb73d687ac4f571eab3d507a94f511e9f3d387a64f4b1e933d207a34f451e873d087a04f3f1e7b3cf079d4f391e6f3
|8,3=>0x73a3e6e7cd0f989f2e3
|9,0=>0x1ee4bdb97b52f665ec4bd797ad2f565ea4bd397a52f465e84bcf979d2f365e64bcb97952f265e44bc7978d2f165e24bc397852f065e04bbf977d2ef65de4bbb97752ee65dc4bb7976d2ed65da4bb397652ec65d84baf975d2eb65d64bab97552ea65d44ba7974d2e965d24ba397452e865d04b9f973d2
|10,0=>0xf843f047e00fbf1f7c3ef47de0fbb1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x14000000000024000000000044000000000086000000000108000000000208000000000400000000000680000000000c00000000001200000000002000000000003a0000000000580000000000a0000000000120000000000220000000000400000000000780000000000c0000000000140000000000240000000000440000000000800000000000c0000000000140000000000200000000000300000000000500000000000800000000000800000000000800000000000
|1=>0x3432000000006410000000009060000000012080000000022080000000041280000000080600000000100400000000167a0000000024f40000000049680000000084000000000104000000000203000000000402000000000800000000000cc400000000102800000000202000000000402000000000800000000000ca00000000019200000000032000000000045800000000088000000000104000000000200000000000240000000000410000000000800000000000a2
|2=>0x458ce0000000848b00000001090600000002100c0000000416da0000000828bc00000010487800000020208000000040020000000080030000000100040000000200040000000310c40000000290980000000500000000000808e00000001004800000002003000000004000000000004022000000008040000000010000000000015168000000024220000000048000000000082080000000101200000000201000000000401c00000000803000000001000000000001a2d
|3=>0x2412da0000004825740000008200000000010243f0000002034da000000402194000000804000000001003280000002006480000004002f80000008004b0000001000800000002000920000004000a00000008000600000010000100000010325a00000020443000000040018000000080024000000100028000000200044000000400040000000800040000001000020000002000000000002001800000004002000000008002000000010001800000020001000000040000
|4=>0xa012da0000014021f40000028043780000050086d000000a0025e0000014001b00000024043680000048042f00000084000000000100a9bc00000200696800000400a2f00000080125e000001002194000002004178000004000790000008000ea0000010001bc00000200006000000400001000000800000000000c8253000000180c3600000021000900000040349800000060003000000090d3e800000121a4d0000002432fa0000004848a00000009090600000012102c
|5=>0x1000010000002000000000003ac44100000074086a000000e311d4000001c465e40000038043780000070086d000000b010fa0000016021b4000002a0455800000521c7f000000a434fa0000014869bc00000290d3680000052097d000000a410fe0000014821b40000028843780000051086d000000a100f200000140b23c00000281637800000501c6f000000a032da0000014061fc00000280c3780000050186d000000a016da0000014029fc00000280537800000500a6d
|6=>0x4a010fa0000094021bc0000128043680000248196f0000049032da000009000090000010c0cb68000021811240000042412fa00000844028800001080ca2000002101124000004202218000008402df40000108053680000208112c00000410024800000820005000001020435800002020b510000040032ca0000080060f400001000536800002000a0f0000040002080000080000880000100000a0000020000040000022000020000040000040000048000000000080002c
|7=>0x82006480000104008b0000020800080000041000000000080432a000001001021000002001467800004000b750000080016d20000100028f40000200049e80000400032c0000080006500000100008800000200009000000400002400000800004000001000004000002000002000004000000000004e210fe000009c421f400001380c1f80000259196d000004b032de0000096065b400001280cbf80000250197d000004a030fe0000094061f40000128053e80000250087f
|8=>0xc20104e0000144021300000238043e80000470084d000008c010980000114821f400002281627800004500f7f000008a016de000011402db40000228053f800004500a7d000008a012fa0000114021fc0000228043e80000450086f000008a010da000011402134000022005b78000044000100000084016d80000104861f400002090415800004101a7d0000082034d20000104061f400002080c36800004100b710000082016da0000104029b40000208042600000410032c
|9=>0x600400180000c00000200001220843200002440087d0000488010ea0000814021b40001001000600001640087d000028a010fa0000510021b40000a20001600001250087d000020a010da0000400800200000800001000000a0000a0000010a000d20000204000100000400000c00000800000c00001000000c0000200000100000400000100000800000000000ca410fe0000194821f40000328043e80000642087d00000c2410fa00001848212400003090422800006100a7d
|10=>0x80e232d8000101c2b1bc00020380cb680004070186f000080e014de000101c029b4000203804b780004070086f000080c0303c0001015621bc00020298d3680004053097d000080a230da0001014425b400020280e1680004050087d0000808b10dc00010100a8bc000202005b680004012197400008024305e000100482dd000020090436800040100b6d000060a410da0000c10821640001821001400003042000c0000600610d80000c008217400018010016000030020028
|11=>0x420a010da0008410821f4001082004368002100108640004088000580008100000800010128043e80020242087d0004040000480008014821f40010028043680020042086d0004008210d800070146b338000e028d4678001405188ef000208a0d0de00041140333c0008208322300010400608c000200a0599e00040140a3bc0008028047780010010082b00020000410c00040000203c000800000590000c060ac6e000088e010fe0001104029b40002208051780004410096d
|12=>0x4000a010fa006004c4202400c00908404801000721a6d002000e030da0030054621bc00600a88436800c0111000c001802020018002011002db4004002084b780044071896e000880e310de001101c425b00022038843600044030186c000800e310dc000889c021b40011128043e80022250086d0004448010da0008880000b00011028043680021450087d000428a010da0008510021f40010a20043680021440002c0004288000480008500000b00010920043e800212020851
|13=>0x20080e911d4040101d221ac080012a043581000054086f020000000124020889c421f40410138843e80800271197d010004e212fa020009c421f40400028043680800010086c0080008410c80100010000000131038843600260061086c004880e210da009101c401b00122038003680242071086c004800e210d8008881c021b40110a38043680221060086d0044208410ea008801c021b40110029843e80220051086d004040a210da0080518021b40100838043680201051086d
|14=>0x908000c2001301100100009181220288436a0203070086d400080a216da409101c001b48100028043e88440051086d100428a210da2008014421b421020000036820000000000020214a010de04042840016c080850000540101005408eb
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x90000800000880000000b0240000010200000
|6,0=>0x8c00005f8ac300904824002200000002105824a600049109a12390000000081587c000480c44ec001040032000000000000005631048200c0600044000904809d807208e032020000004020909800000300804099506400be7800c06340012c1ec204af400080180000423003c0a091200000170103c00320000022000002c22111f8640c66118080066199280ac6
|6,1=>0x604f2890404150000c0423
|7,0=>0xddcf5147e90ec92a259ddcde11b0d149786f218708493639b9379d9882836cfda1e9f6f32a99050ef3a3c69a376408ce757b8c241091655a138ef1adea9fbe03336618f364a98249a483a5640339872e2c96874fa89b90a0b487311232a3a1d8b6f8681b47d18d531ec6f40349005973f30852f539161aa88d3a626406545dd95ea45150f608288f591f82f7e545deea
|7,1=>0x9ca55a9e2bd85ecc3a33dd1707a183c1e2da16fd6a2e238f2ee900484abe01a52ad29b0953321c4678011884b258ec53003bbc8729c0509d1c9a3ccc662092c9c40c652e80cb881ca2125cc7d9c0665a7751d617807c162cc1ea0001da509f081e2ba9125de2706b59c24014bf11f2553c00659966017f214b770b528985f13a02410416cd24c7480df4db55220361f
|7,2=>0x251c5145397ec909a3ccd2f
|8,0=>0xe7bfeb5c6065be2f5b7ea199d547439ed8d73fd22db5e694cd8b36d6ede4cacb858a40d470179a1937a272005ec160b879b9d2991b6ac26f1a2c4ae58383a39e2b34b36e75acf71cbc28345385a575b0e4a85f6fb6936f2f73a8c0a93069c91d041b6e7fa0dfe806ec0e1ea9dabf94bcc6ecce159c86ae4ff08d766b3f8eab6f619a08c6495f75d66170b74a24d6b2b3
|8,1=>0x136cee24e1372a8392b68d2a380d9cf60f153a4b48e21914f40b30a2e5369d715e11af75a9c362cf8b7d52cb8f19c6c92a6dc2f6adbd06b1c96d345812baab054e5fa06823b214f741bda91c6a4
|9,0=>0x6be67a1706331387ccb7eb1af5649a8eb0733923588b4c4948b3baac74ca0bcd494adf50dda1ea751aa622e1db45223c8c6d1f9ab1d2375cd138ec9669379d54dc49fbfc5ab58c
|10,0=>0x504cd3a9f6fdd57111
|11,0=>0x9c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 47 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_205 7 roots_205 ops++addP pm 2 dom_249 9 roots_249 ops++addP pm 3 dom_189 9 roots_189 ops++addP pm 4 dom_57 5 roots_57 ops++addP pm 5 dom_125 9 roots_125 ops++addP pm 6 dom_237 10 roots_237 ops++addP pm 7 dom_173 7 roots_173 ops++addP pm 8 dom_157 6 roots_157 ops++addP pm 9 dom_217 6 roots_217 ops++addP pm 10 dom_233 8 roots_233 ops++addP pm 11 dom_213 8 roots_213 ops++addP pm 12 dom_93 6 roots_93 ops++addP pm 13 dom_201 5 roots_201 ops++addP pm 14 dom_169 5 roots_169 ops++addP pm 15 dzo_204_1 5 roots_204 ops++addP pm 16 dom_188 7 roots_188 ops++addP pm 17 dom_121 6 roots_121 ops++addP pm 18 dom_109 7 roots_109 ops++addP pm 19 dom_29 4 roots_29 ops++addP pm 20 dom_221 9 roots_221 ops++addP pm 21 dom_124 7 roots_124 ops++addP pm 22 dom_245 9 roots_245 ops++addP pm 23 dom_105 5 roots_105 ops++addP pm 24 dom_220 8 roots_220 ops++addP pm 25 dom_61 6 roots_61 ops++addP pm 26 dom_185 6 roots_185 ops++addP pm 27 dom_45 5 roots_45 ops++addP pm 28 dom_241 6 roots_241 ops++addP pm 29 dom_117 6 roots_117 ops++addP pm 30 dzo_220_1 6 roots_220 ops++addP pm 31 dom_232 7 roots_232 ops++addP pm 32 dom_141 4 roots_141 ops++addP pm 33 dom_181 6 roots_181 ops++addP pm 34 dzo_252_1 7 roots_252 ops++addP pm 35 dom_156 5 roots_156 ops++addP pm 36 dom_92 5 roots_92 ops++addP pm 37 dzo_244_1 6 roots_244 ops++addP pm 38 dom_244 8 roots_244 ops++addP pm 39 dom_60 4 roots_60 ops++addP pm 40 dom_77 4 roots_77 ops++addP pm 41 dom_41 4 roots_41 ops++addP pm 42 dzo_236_1 6 roots_236 ops++addP pm 43 dom_180 5 roots_180 ops++addP pm 44 dom_184 5 roots_184 ops++addP pm 45 dom_248 8 roots_248 ops++addP pm 46 dom_116 5 roots_116 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_204_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_220_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_252_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_244_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_236_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_116 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 138 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 138 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 266 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 266 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 197 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 69 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 197 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 63 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 63 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_slice_b [(0x5555000055550000555500005555000055550000555500005555000055550000,4,20)] (by decide +kernel) lowS_238
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,96),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,80),(64,96),(64,192),(65,67),(65,69),(65,73),(65,81),(65,97),(65,193),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|9=>1
|10=>5
|11=>8
|12=>3
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xff777
|10,0=>0xdc7f7accb571a0726bba25344
|11,0=>0xa30979c2648713266f0c51a4a4ea87395c70ba42
|12,0=>0x792e461eec0c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffffffffffffffffffffffaaffaaffaaffaaffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa
|0,1=>0xffffffffffffffff0000000000000000ff00ff00ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x28d020a9273148310549398a810409398ad22041524e62a2020a927315a810549398a44082a71cc52204161cc51a041624e6290620a9c62bd02081273148810407315a44082c398a41882b498a418820
|1=>0xc54082a49cc54082a724e62a0415a4e6
|_=>0
def sO:Nat→Nat→Nat
|9,0=>7
|10,0=>0x2982091880f9078
|11,0=>0x6f96785da5494b94293a8319
|12,0=>0x899818789
|13,0=>0x928
|_,_=>0
def wAt:=mkWire dB 17 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x49d51d41d42541d53949d21d4251a741d1a541d3a542552542552541d49d42541d40153949d5393a542552521d42551d42541d5a551d42541d
|_=>0
def oO:Nat→Nat→Nat
|9,0=>4
|10,0=>0x10334ca31cc43
|11,0=>0x849f2749b26497254932
|12,0=>0x25190631
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xe3ff83ff83fe1fcf17cf13ff13cf0fdf0fcf0bcf07df03fe03ef03df03cf0000
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>4
|10,0=>0x6fd8a
|11,0=>0xbec9c752
|12,0=>0x639
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 16 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_247 11 roots_247 ops++addP pm 4 dom_190 10 roots_190 ops++addP pm 5 dom_126 10 roots_126 ops++addP pm 6 dom_239 12 roots_239 ops++addP pm 7 dom_223 12 roots_223 ops++addP pm 8 dom_191 11 roots_191 ops++addP pm 9 dom_127 11 roots_127 ops++addP pm 10 dom_183 8 roots_183 ops++addP pm 11 dom_63 9 roots_63 ops++addP pm 12 dom_119 8 roots_119 ops++addP pm 13 dom_182 7 roots_182 ops++addP pm 14 dom_118 7 roots_118 ops++addP pm 15 dom_62 7 roots_62 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_62 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 5 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 8 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 8 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [11, 8] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 14] }, { op := GateOp.and, inputs := [13, 12] }, { op := GateOp.and, inputs := [10, 9] }, { op := GateOp.and, inputs := [3, 15] }, { op := GateOp.and, inputs := [7, 6] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52874_aux

theorem PEqualNP.Outside.L_meta_52874 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52874_aux.main
