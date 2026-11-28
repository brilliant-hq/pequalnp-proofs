import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51884_aux
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

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffaaffaaffaaffaaee00ee00ee00ee00ffaaffaaffaaffaaee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffafffafffafffaee00ee00ee00ee00fffafffafffafffaee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafa0000fafa0000fffffafafffffafafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffff00ffffff00cc00cc00cc00cc00ffffff00ffffff00cc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffaaffffffaaeeaaee00eeaaee00ffffffaaffffffaaeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaa00fafaaa00fffffffafffffffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffff0fffffff0fcf0cc00fcf0cc00fffffff0fffffff0fcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffafffffffafefaee00fefaee00fffffffafffffffafefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefafafafafefefefe00000000fefefefefafafafafefefefe00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccff00ff00ffccffcccc00cc00ffccffccff00ff00ffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffaaffaaffeeffeeee00ee00ffeeffeeffaaffaaffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafffafffaaa00aa00fffafffafffafffafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfff0fff0fffcfffccc00cc00fffcfffcfff0fff0fffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffafffafffefffeee00ee00fffefffefffafffafffefffeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffaaaaeeeeeeeeaaaa0000ffffeeeeffffaaaaeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f0f0f00000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafafafa0000fffffafafffffafafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffff0f0fcfcfcfcf0f00000fffffcfcfffff0f0fcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffafafefefefefafa0000fffffefefffffafafefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaaaa00ffffffaaffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffff00ffccffcccc00cc00ffffffccffffff00ffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffaaffeeffeeeeaaee00ffffffeeffffffaaffeeffeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffafafaaa00fffffffafffffffafffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffff0fffcfffcfcf0cc00fffffffcfffffff0fffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffafffefffefefaee00fffffffefffffffafffefffefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafafafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefefefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffefffefffeee00ee00fffefffeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffefffefefaee00fffefffefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefefafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffaaffaaffaaffaaee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfff0fff0fff0fff0cc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffefffafffafffafffaee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffaaaaffffaaaaaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffff0f0fffff0f0f0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffafafffffafafafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffffff00ffffff00cc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffffaaffffffaaeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffafffffffafffffffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffffff0fffffff0fcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffefffffffefffffffafffffffafefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffffafafafafafafafafafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffefefefefefefefefafafafafefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffccff00ff00ffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeffaaffaaffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff0fff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafffafffafffafffafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffcfff0fff0fffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffefffefffefffefffafffafffefffeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeffffaaaaeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffffffafafffffafafffffafafafafafafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcfffff0f0fcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffefefffffefefffffafafefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffaaffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffffccffffffccffffff00ffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffeeffffffeeffffffaaffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffffff0fffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffffffafffffffafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffffcfffffffcfffffff0fffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffefffffffefffffffafffefffefefaee00
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
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_41
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
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
|0=>0x14815240925545514055248550405
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
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_45
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_45
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_27
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_45
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_45
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_45
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_45
def isoMvS_120:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_45
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_45
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_45
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_45
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_45
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_45
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_170:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_169
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_45
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_43
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
|0=>0xf9c80
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dzo_46_16 5 roots_46 ops++addP pm 2 dom_60 4 roots_60 ops++addP pm 3 dom_42 4 roots_42 ops++addP pm 4 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_60 _ g hchk
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xcccc000000000000cccc,8,10)] (by decide +kernel) lowS_77
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,68),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(64,65),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x333300000000000033330000cc00cc0000000000cc00cc030303030000000003030303088888888000000008888888b33333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 94 0x3fffffffffffffffffffffff
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
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_85 5 roots_85 ops++addP pm 3 dom_77 5 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_92 5 s (0,roots_92.map (·&&&dom_92)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_92 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_93 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_slice_b [(0x3030000030300000303000003030,32,36)] (by decide +kernel) lowS_105
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
|0=>0x92095191a91a90407191091292
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x51410000220000001101
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffbce848f30a200
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3400500261
|6,0=>0x7898
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_156 5 roots_156 ops++addP pm 1 dom_154 5 roots_154 ops++addP pm 2 dom_148 4 roots_148 ops++addP pm 3 dom_138 4 roots_138 ops++addP pm 4 dom_142 5 roots_142 ops++addP pm 5 dom_150 5 roots_150 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_158 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_150 _ g hchk
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
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xa0a00000a0a000000000000000000000a0a00000a0a,8,9)] (by decide +kernel) lowS_170
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030,32,36)] (by decide +kernel) lowS_169
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_slice_b [(0x2200220022002200000000000000000022002200220022,16,17)] (by decide +kernel) lowS_180
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_slice_b [(0x50500000505000000000000000000000505000005050000,128,144)] (by decide +kernel) lowS_170
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_62
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_55
def isoMvS_107:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_93
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_61
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_62
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_109
def isoMvS_118:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_62
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_93
def isoMvS_122:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_62
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_47
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_47
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_93
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_174:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_173
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_93
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_93
def isoMvS_185:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_173
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_93
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_55
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_93
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_109
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_61
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_59
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_181
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_59
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_181
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_61
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_109
def isoMvS_229:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_109
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_173
def isoMvS_234:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_186
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_109
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 6:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_61
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
|0,1=>0xccccccccffccffcc00000000ff00ff00ffff3333ffff000000ff00ff00000000ff000000ffff0000cc00cc00ff00ff000000000033003300ffccffccccccccccffffffff33003300ffffffffccccccccffccffccffccffcc00000000ffccffcccccccccccc00cc00ccccccccccccccccff00ff0000000000ffffffffffff0000
|0,2=>0xfff0fff0f0f0f0f000ff0000ffff0000ffffffffffccffcc00cc00ccccccccccffffff00ffff0000ffff00ffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x48150b0ca0920591160ca0920440d80815c328204d1160d508140a0920541031c24842c32822040c248114b0ca0880c24811440d108118b0ca0811902ca08118b0cf08130b2820463840c204d30b0ca2481031c21830811400c20461440c2040
|1=>0xca0920464042ca09204309205c78b0ca0811902ca09205e2e12824812e02824815cb0ca09204b0ca09f4812c360a08158b0d52820442ca09204e2c33ca09204b28248139e2c31ca09210328248134b74a09204b29b09204b0ca0926812c3282
|2=>0xca09204d2c354a09204b0ca09205c2c32824813102d528248110b0ca0930502ca09204c10b0ca0920440d109204b0ca0930442c35424812c394a4812ca0920648cb0ca09204b0d509205e10b0ca0811842c309204c2c32820622c328204d30b
|3=>0xb0ca0920562c328248110b0ca09204b0ca09205e40b2824812c329109204b28248138b
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
|0=>0xb492ca4b2a2c34b282c38b4b2924b2b292cb0d2c34b292ca04482ca4b294424b280d1cb282ca8b292ca514a2ca0b2a2cac44b2ca43452ca03712cad1492ca0b294414b282ca43352d2c3732caca372ca51492ca4b282ca4b294414b284c144482ca44472ca4b28
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa30009100063000000cc03000000000000000
|6,0=>0x301002f1002d2acaa1a0a62002519063184800000007c9d2001b26480000172001610000050931448f238400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf3fcde7f5fd774fc3709c04e83048b2108214450110421002a07c1a0180400c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc050204230c0000000
|6,0=>0x5111d0396330108f6800a88533a00111300992eb358005
|7,0=>0x31ad5b77be779
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_29 4 roots_29 ops++addP pm 2 dom_61 6 roots_61 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_54 4 roots_54 ops++addP pm 6 dom_31 5 roots_31 ops++addP pm 7 dom_55 5 roots_55 ops++addP pm 8 dzo_47_16 6 roots_47 ops++addP pm 9 dom_47 6 roots_47 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_47 _ g hchk
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
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000ccc8cc00
def gsh_93_2:=0x333333320000000033323300
theorem lowS_zo_93_2_85:Lower true dzo_93_2 roots_93 gzo_93_2 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_85)
def dzo_85_2:=0xcc00cc0000000000cc00cc
def gzo_85_2:=0xcc00c80000000000c80000
def gsh_85_2:=0x3300320000000000320000
theorem lowS_zo_85_2_85:Lower true dzo_85_2 roots_85 gzo_85_2 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_2) [(dom_85,2)] (by decide +kernel) (lower_slice_b (T:=gsh_85_2) [] (by decide +kernel) lowS_85)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(3,11),(3,19),(3,67),(4,20),(4,68),(5,13),(5,21),(5,69),(6,14),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,82),(24,25),(24,26),(24,28),(24,88),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x44f983d51c01dec
|5,0=>0xdbd85d96cf84b6c814366b55a6667d616d2419c0339792fe2a
|6,0=>0xf8e2df4153d6302c9547c75f0c0be3af52e9323b700976f9fe6f78a654e262b886055f4fe621bd920c6f3
|7,0=>0xfddb0e1246da081bf2a14d1952bb092a996
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f000f000000000f0f00003300ffff0000000033003300ffffffff00000000ccccccccffffff0000000000000000003300330000000000330033000f0f0f0f000000000f0f0000ffffffff0000000000000000ffff000000000000ffff0000ffffffff00000000ff00ff00fffffff000000000f0f0f0f0aaaaaaaa00000000aaaaaaaaffffffff00000000ffff0000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f0cccccccc00000000ccccccccffffffaa00000000aaaaaaaa
|0,1=>0xff00000000000000000000000000000000ffffff00ffffffff000000003300330000ff00ff0000000000ff0000ff00ffff00000000ff00ff0000ff00ff0000000000000000ffff00ff00000000ffff0000ccccffff00000000ccccccccffffffff00000000ffffff000000ffff000000000000ff000000ffff0000000000000000ffffff0000000000ffffff000f0f0f0f000000000f0f0f00555555550000000055555500
|_,_=>0
def sP:Nat→Nat
|0=>0x104a962062b152440c455a6a818825491030954940c412d128188ab4ce48388254a0612c528188304a0e209588184af4a06609528188ae4a06d2a92418825620655a928188204a0e208083304a418820
|1=>0x40c412a5031156940c412a67240c412a503104a9c20e3104a940c4d2a488188254a0612a928188254f788188254c883104a940c45da503104ba4a323104a9220626953740c412a503
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb96b27ab7a479e69779078978277b77566e76776075975274b7
|7,0=>0xe86e17da7d37cc7c66bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18742640d1a61a50a542520b42592640d92740d40d4255a518720f4251cd4264250a54611a692440d0cd42618742541d1a520b42518742640d1a5
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a26096250922408e2308a2208621080008802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xfffded7d6f6d684b3924201c18090600
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x233983365c8676014
|7,0=>0xbdceefd
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_94 7 roots_94 ops++addP pm 1 dzo_93_2 6 roots_93 ops++addP pm 2 dom_79 6 roots_79 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dzo_85_2 5 roots_85 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dom_85 5 roots_85 ops++addP pm 7 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_94 7 s (0,roots_94.map (·&&&dom_94)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_94 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_107
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
def dzo_81_2:=0xc000c00000000000c000c
def gzo_81_2:=0xc00080000000000080000
def gsh_81_2:=0x300020000000000020000
theorem lowS_zo_81_2_81:Lower true dzo_81_2 roots_81 gzo_81_2 4:=lower_iso_b (d1:=dom_81) (r1:=roots_81) (T1:=gsh_81_2) [(dom_81,2)] (by decide +kernel) (lower_slice_b (T:=gsh_81_2) [] (by decide +kernel) lowS_81)
def dzo_42_16:=0x505000005050000
def gzo_42_16:=0x504000004000000
def gsh_42_16:=0x50400000400
theorem lowS_zo_42_16_42:Lower true dzo_42_16 roots_42 gzo_42_16 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_16) [(dom_42,16)] (by decide +kernel) (lower_slice_b (T:=gsh_42_16) [] (by decide +kernel) lowS_42)
def dzo_113_2:=0xc000c000c000c000c000c000c000c
def gzo_113_2:=0xc000c000c0008000c000c00080000
def gsh_113_2:=0x30003000300020003000300020000
theorem lowS_zo_113_2_81:Lower true dzo_113_2 roots_113 gzo_113_2 5:=lower_iso_b (d1:=dom_113) (r1:=roots_113) (T1:=gsh_113_2) [(dom_113,2)] (by decide +kernel) (lower_slice_b (T:=gsh_113_2) [(0x30003000000000003000300000000,0,32)] (by decide +kernel) lowS_81)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c080c0c0c0c0c080c00
def gsh_121_2:=0x3030303030303020303030303020300
theorem lowS_zo_121_2_81:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3000300030003000300030003000300,0,8),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_81)
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c08000000000c080c00
def gsh_89_2:=0x30303020000000003020300
theorem lowS_zo_89_2_81:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30003000000000003000300,0,8)] (by decide +kernel) lowS_81)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(18,19),(18,26),(18,50),(18,82),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,65),(64,72),(64,80),(66,67),(66,74),(66,82),(66,98),(96,97),(96,98),(96,104),(96,112)]
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
|4,0=>0xbf2592e71c2cdbc2b10a21e2d144df114b1
|5,0=>0xd7dedb85d2a8006a0325940398d61d7cd966e3e656ce83c10f376a32d74c286a62197f1d42312494117ce091b3
|6,0=>0xe3d5fd8dd0bb218a73fc9ee0b9c18197d44948e28e4d88b5d288d08822f1800377dd797d0b3767bc749e9703776903c67aeb5e77559cec587dc44ed6436d2436d03f0493d8d83cd203833437db42903626a5623eb71ddb31dd3718f9e17402107f50d1770c09c0acad0a72c05d3a02a4b024bd
|7,0=>0xdbc5cc7803c023eb3367ae6f79314a8eb9b8532078e10779817593d72958713776f6ab60c6f5f86f52ca74f644496ca446b53c00a3b21c391042e1d02cd922c9172a9472a03921efa1fafa1d93e1992e1489e0d55c0ca2c001c7
|8,0=>0xcdd92a269a93d0378ef06900d62b5b47c6832d0c1cf4b1b6780e7a107721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xe0e0e0e0e0a0e0a0e0e0e0e0e0a0e0a0000f0f00000f0f00000e0e00000e0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f000f0f0f0f0f0a0f00f0a0f0a0f0a0f0a0f0a0f0a00000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f000f0f0f000f0a0f000f0a0f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f000f000a000a00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
|0,1=>0xf0f0f0f0f0f0f0f000000000f0a0f0a000000000000000000f000f000a000a50505050505050505000500050005005050505050505050505050500000000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f00000f0f00000a0a00000a0a000000000000f0f0f00000000000f0a0f003030303030003000303030303000300f0f0f0f0f0f0f0f0e0e0e0e0e0a0e0af0f0f000f0f0f000f0f0f000f0f0f0000000000f0a0f0a000000000f0a0f0ac0c0c0c0c000c000c0c0c0c0c000c0000000000f0f0f0f000000000f000f000000f0f00000f0f00000a0a00000a0af0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00
|0,2=>0xf0a0f0af0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0000000000000000f0f0f0f0a0a0a0a0050005000500050005000500000000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af000f0f0f000f0f0f000f0a0f000f0af0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f050505050f0f0f0f05000500a0a0a0a0f0f0f0f0a0a0a0a0f0a0f0a0000000000000000f0a0f0a0f0a0f0af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a00000000f0f0f0f000000000f0a0f0af0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0a0f0ae0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000f000f000f000f000a000a
|0,3=>0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f00000f0f0f0f0f0f0000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000f0f0f00000000000f0f0f0000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0000000000000000e0e0e0e0e0e0e0e404040404040404040404040404040400f0000000f0000000f0000000f0000a0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x40f2110d03c92076c30802044464001440d00401511801592114056122040d05091510d05cf2110ca30014d58201521141415220d10308c0071030802510c20094c70ca00521140f4884503ce20d0ca3002c41801470ca0091c41801440c2040
|1=>0x40014844340915821158200554844331000571b4433100051110c230015b3510d08483430900152110d000580844340015f21b4430900081cd0c200844340015e2040d050520444340015d4434142452070d00057084430810086d10c2300103
|2=>0x4001510ca40014811158c0051c40d00091510d00091531110e34001510d0005b084560a1211ac340560846a400148a510d00091510c2990009a110d00052110e39900054434010052110d002714844398c400165456080148443400164222443
|3=>0xcc0148456405c883440d00052110d05052110c24001552110d0005748450172c481d10c200520d4564001483510c230020744308024844340f2110d003014844340016f21119000522e450005488351582008b510c24002044430900093440cc
|4=>0x20746b0d00052044430900052110cc405c884564001762110c242121b1110d00052110d015820d44331000522944331000520744340024522d4434001484434001752044434002459510c2400148a510d00052110c23001484434340052110d0
|5=>0xd000521158340014844340014844340024520d443400148e110d00052114001712110d084520444340014845642114846b0f74001481114001712044434211484434001552253510d000521158c0052110e3400148b910d00091481cd0d0005
|6=>0x110d00052110c24001484790d000522e44340014846b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f547761c586b619585f61658536135847610583b60d582f60a58236
|6,0=>0x6fddb876cd5ac7695d9f6661d92662dd8475f5d7675c19697589d5b7551d4f5521d4264edd3474b5d26747dd187445d0a740dcfc73d5cee739dce07365cd2732dcc472f5cb672c18a9728d89c7255c8e7
|7,0=>0xb01ab88ac5eaa7a8de9b8a55a8e7a1a27f79de26f89a1e61796da538935a4588f623588b9e277881e188845e0a780ddfc77d99ef77a59e18769dd46735dc67
|8,0=>0xc41f097c09efb7bd1eee6b9dee07b65ed36b35ac67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd04541463452100790450d0424715044174484945148511500542471505b43091c8351515045151454100708454114c1740845210071045105c84534c111540844154485121505401c4114521348454569043241485a410c905212054f21505401c4114408448452110208451484521
|1=>0x14848860054341005c545211401c41142471504c1740840170d0c54141145450d04521505401c41144436904324148432614843411514541348c545102101544851212104341148502514850150d0401500790454124326148444144842234054c178c8d02534c102115163233055021
|2=>0x405430101143150d0452115143450d0c015448434100550010c551210d0c01544842471504d4115148410d0502514851011484545411450d41150154484841005d6470d040154054415448401e41150211514c4540851411484d23151444321151211484245150481d41150214054025
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000001000
|5,0=>0x1b31921541411220f30000c30000b1074052000000000041000022
|6,0=>0x6c16936810006536326035e20000005b35835710005520005235024d34b24924814624330004033e20003c23a23733523320003122f22e12d12b22830002532322031e2
|7,0=>0xb32b12af2ad2ab2a92a72a52a32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d2
|8,0=>0xbf1be1bd1bc1bb1000ba1b91b81b71b61b51
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x181000060000011b400023d0000880000210000082000020500008000001ed00006bc0001ae00006b40001ac00006a400010000002b0000070000014000004000000e4000021000008000001800000400000090000020000006000000c0000020000004000000
|1=>0x2327f40889fd02101e00400710100164023bbd00866f40209ad00406b400fbad003aff000b9ad0025eb4005fad0016eb400580d0011804004209000eef4003a29000cfb400200900066f40019ad00061e40018690004fb4000ded00036b400067d0001940000620
|2=>0x842c6b51239ad20286bc80208b10884042209af088040c1c17a50625e941881ad05061e41417ad05046b4121fad04866f41219ad04856f40c0621
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x400100
|5,0=>0x3051e08289002400208140000030008
|6,0=>0xc287803720b0c973489a8c008003a02a80981abc3005c38021022cc990e7c51e3c65300246c185
|7,0=>0x753524152edb32971e71c4ad1cc07071e9d8cfa4bc7ec22425728a8b62593ad
|8,0=>0x514264f68459c5a28e1c8
|9,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_73 4 roots_73 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dzo_81_2 4 roots_81 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dom_81 4 roots_81 ops++addP pm 7 dom_107 7 roots_107 ops++addP pm 8 dom_121 7 roots_121 ops++addP pm 9 dzo_42_16 4 roots_42 ops++addP pm 10 dom_42 4 roots_42 ops++addP pm 11 dzo_113_2 5 roots_113 ops++addP pm 12 dzo_106_16 5 roots_106 ops++addP pm 13 dzo_107_16 6 roots_107 ops++addP pm 14 dom_51 4 roots_51 ops++addP pm 15 dzo_43_16 5 roots_43 ops++addP pm 16 dom_41 4 roots_41 ops++addP pm 17 dzo_121_2 6 roots_121 ops++addP pm 18 dom_90 4 roots_90 ops++addP pm 19 dom_27 4 roots_27 ops++addP pm 20 dzo_89_2 5 roots_89 ops++addP pm 21 dom_89 5 roots_89 ops++addP pm 22 dom_113 5 roots_113 ops++addP pm 23 dom_106 5 roots_106 ops++addP pm 24 dom_105 5 roots_105 ops++addP pm 25 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_81_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_113_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_121_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_89_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(96,97),(96,100),(96,104),(96,112)]
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
|5,0=>0xcd8f4ace6f76423
|6,0=>0x393fc37917204bc0406700ecb
|7,0=>0xb324d8e2268d60a53413
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33333300333333003333330033333300cccc8888cccc8888cccc8888cccc888b3333333333333333300330033003300cccccccccccccccccccccccccc00cc030303030303030303030303030303030888888888888888888888888888888880003333000033330000323200003232cccccccc00000000cccccccc000000033333333333333333333333322222222cccccccccccccccc00000000000000033333333333333333333333300000000cccc0000cccc0000cccc0000cccc00033003300330033003300330033003300c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8cb3333333333333332222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x732a95732195732a0957e32a957d32a9543c2a96432a95432195b432a95432a0972198564321543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b648e798bb916
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
|0=>0x2a5954c9395d5255d5756a5755d5955d5
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x100
|6,0=>0x7261423112
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x9fd4803ed37d1fd016006000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>8
|6,0=>0x54f4
|7,0=>0xedb
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_92 5 roots_92 ops++addP pm 2 dom_116 5 roots_116 ops++addP pm 3 dom_61 6 roots_61 ops++addP pm 4 dom_124 6 roots_124 ops++addP pm 5 dom_109 6 roots_109 ops++addP pm 6 dom_93 7 roots_93 ops++addP pm 7 dom_117 6 roots_117 ops++addP pm 8 dom_45 5 roots_45 ops++addP pm 9 dom_29 4 roots_29 ops++addP pm 10 dom_85 5 roots_85 ops++addP pm 11 dom_120 4 roots_120 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_120 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
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
def dzo_124_2:=0x44444444444444444444444444444444
def gzo_124_2:=0x44444444444444404444444444404400
def gsh_124_2:=0x11111111111111101111111111101100
theorem lowS_zo_124_2_84:Lower true dzo_124_2 roots_124 gzo_124_2 6:=lower_iso_b (d1:=dom_124) (r1:=roots_124) (T1:=gsh_124_2) [(dom_124,2)] (by decide +kernel) (lower_slice_b (T:=gsh_124_2) [(0x11001100110011001100110011001100,0,8),(0x11111111000000001111111100000000,0,32)] (by decide +kernel) lowS_84)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,56),(24,88),(32,34),(32,36),(32,40),(48,50),(48,52),(48,56),(48,112),(64,68),(64,72),(64,80),(66,70),(66,74),(66,82),(66,98),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aaaaaaa800000002aaaaaaa8000000055550000555500005555000055550000aa00aa00aa00aa00aa00aa00aa00aa0141414141414141414141414141414142222222222222222222222222222222255555555555555550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>6
|_,_=>0
def wAt:=mkWire dB 6 127 0x7fffffffffffffffffffffffffffffff
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
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_62 7 roots_62 ops++addP pm 2 dom_118 7 roots_118 ops++addP pm 3 dom_94 7 roots_94 ops++addP pm 4 dom_124 6 roots_124 ops++addP pm 5 dzo_124_2 6 roots_124 ops++addP pm 6 dom_110 6 roots_110 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_124_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_110 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_126 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_126 roots_126 goal_126 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_126
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=S_126.noCircuit
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_174
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_42:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,144),(18,19),(18,26),(18,50),(18,146),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x4b53d0a8d3
|6,0=>0xd38a6ae7e488f275b9765b3ed312203045f09edb
|7,0=>0xc3cc4bf55c8852f6494852dbc3082822f9a0aba606719
|8,0=>0x6a88837c7026f6b
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f000000000000000000000f0f0f0f0f0f000000f000f000f00000000000000000000000f000f000f000000000000f0f0f000000000000000000000000000f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0000000000000000000000000f0f0f0f00000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00f0f0f0f0f0f0f0f00000000000000000f000f000f000f00a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a30303030303030300000000000000000303030303000300f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf000f000f000f0000000000000000000f000f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x524c2020a93080520cc2030aa498407946930805524c2801872a9261016550cc201526138072a869309855244102cea1984552441020e9308072906611caa4882028cc26818520cc2020e3308a418820
|1=>0x5524c201543498407952610165
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3773162b62561f61871260b7
|7,0=>0x7566f66876175a75284b74563e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4815152a55a92a54815255812a548151549e28149d2814812a57a75152814815812a52a528148161b5812a55a928149552528148161b49d2924815254a928d4814815a9281495
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x6095348cf330ca21cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x1cf3e6863ce1e6cf35fdaf6d1e64f32600fdc7be2df0fb876c1e6080038810001e000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20
|6,0=>0x23068708cb
|7,0=>0x97d1519c0f2
|8,0=>0x34ec
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_139 5 roots_139 ops++addP pm 3 dom_163 5 roots_163 ops++addP pm 4 dom_179 7 roots_179 ops++addP pm 5 dom_171 8 roots_171 ops++addP pm 6 dom_155 7 roots_155 ops++addP pm 7 dom_185 8 roots_185 ops++addP pm 8 dzo_171_16 6 roots_171 ops++addP pm 9 dzo_43_16 5 roots_43 ops++addP pm 10 dom_147 5 roots_147 ops++addP pm 11 dom_51 4 roots_51 ops++addP pm 12 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_189
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(24,25),(24,28),(24,56),(24,152),(32,33),(32,36),(32,40),(32,160),(48,49),(48,52),(48,56),(48,176),(128,129),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_189.map (·&&&dom_189)
def gM:=goal_189&&&dom_189
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xed44ccd3fe9950d7dd3c603835edc05b06e517024acc63bbfd3a4f7321542ceac2844725d361e8b21ab250dd6106fb101dcd0065e
|5,0=>0xf1d0ce3d34e3007db4cdc3d0cbe3589f47197dce92c828df238d4c38c7638ae8f80e70808207f20b7a2d8798466c14a6beb4679576050b5f3f95c71e5ade4553ab53ab84e91a4d1da4cbcb474264595f3fe8e3f5fe3d6fc3969a346dc33502334ef2de5a2b4332af1928c5f28a8827c462714e26820266dd2630c24d412471a23860236861862213f5912d6c0edb00a9260a2c9049d80353d
|6,0=>0xfdf9eec370e51fcda96fd5daecc005ca308b667bb5f52b2c40aeb10aeaa3aaabca9e9ba2ff597a1091e8d917d4882fa87f9f7fcfe7f2957834976f0374e3269df3675db66a3d62e1b6279c601355fcb258fea5464b53b0e518a54cd494cc484b59d4a500423d540d5440443400373cdc03c0f739a59376de34a2b30379302e92f2342b4b72ab7725ea2246691c8d216ac816845152b31170210ac20c98b0c13d0b02c07ecf07d57043ab0138f00d95
|7,0=>0xfc3c3f20f1c8e74ba8bbb99ffb76a8b53acafd61ac81da95dfa7ca5a440d9cc578c2ee8aba57f0dc7def97879c770d66e0a66949e67bd35d17b593b65894d50dd7508394fec54f2ae4c6ce475a24348140603350e32fcba1f21317fec16478116e70cfad0c34c0b6ab088ec06d62024e1
|8,0=>0xf20f19dd359db9b8014070fdc68be267cf560ace41cd81b1af
|9,0=>0x3abd3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccc0000000000000000888888888888888b33333333333332200000000000000003300330033003300c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c333333332222222200000000000000003333333322222222c8c8c8c8c8c8c8c80000000000000000c8c8c8c8c8c8000333300003333000000000000000000003333000033330000ccccccccc8c8c8c80000000000000000888888888888888b33333333232323200000000000000003333333332323232cccccccccccc00000000000000000000c8c8c8c8c8c8000222222222222222200000000000000002222222222222222cccccccccccccccc0000000000000000000000000000000000000000000000000000000000000003333333333332222cccccccccccc00000000000000000000cccccccccccc000333333333333333300000000000000003333333300000000cc00cc00cc00cc000000000000000000cc00cc00cc00cc0323232323232323200000000000000003232323232323232
|0,1=>0xcccccccccccccc000000000000000000cccccccc0000000010101010101010100000000000000000101010101010000ccccccccccccc8c80000000000000000c0c0c0c0c0c0c0c333333333333323200000000000000003333000033330000cccccccccccccccc0000000000000000c8c8c8c8c8c8c8ca3232323232323230000000000000000232323232222222200000000cccccccc000000000000000000000000cccc888b33333333332333200000000000000003333333300000000cccccccccccccccc0000000000000000cc00cc00cc00cc0333333323333333200000000000000003333000033330000cccccccccccccccc0000000000000000cccccccccccc000333333333333333000000000000000003030303030303030cccccccc8c8c8c8c0000000000000000cccccccc8888888b333333333333322000000000000000022222222222222228c8c8c8c8c8c8c8c0000000000000000888888888888888b33333330000000000000000000000003333333300000000
|0,2=>0xcccc0000000000000000000000000000888b333333300003333000000000000000033333333000000000000c8c80000cccc00000000000000000000c8c80000c8cb33333330101010100000000000000003333333300000000cccccccccccc88880000000000000000cccccccccccc888b333333333332222000000000000000000000000000000004404440444044404000000000000000044004400440044023232323232323230000000000000000232323232323222244004400440044000000000000000000440044004400440000033330000333300000000000000000000323200003232ccccccccc8c8c8c80000000000000000000000000000000003300330033003300000000000000000033003300330022ccc8ccc8ccc8ccc80000000000000000ccc8ccc8ccc8cccb33233323332333200000000000000000000000000000000cccccccccccccccc0000000000000000cccccccc8888888803300330033003300000000000000000033003300220022
|0,3=>0xcccccccc000000000000000000000000ccc8ccc800000000000000000000000000000003333333332323232ccccccccccc8ccc80000000000000000cc00cc00cc00cc00000000000003333000000000000000000000000000032320404040404040404000000000000000000000000000000033333333000000330000000000000000333333330000000000cc00cc00cc00cc000000000000000000c800c800c800c830303030303000300000000000000000303030303030000888888888c8c8c8c00000000000000008888888888888888101010101010101000000000000000001000100010001008c8c8c8c8c8c8c8c00000000000000008c888c888c888c8b333333333332222000000000000000033333333000000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c000333333332222333300000000000000003333333322222222cccccccccccccc000000000000000000000000000000000111111111111111100000000000000001110111011101110
|0,4=>0xcc00cc00cc00cc0000000000000000000000000000000333333333333003300000000000000003333333333330000cccccccccc00cc000000000000000000cccccccccc00cc0000000003333333300000000000000000000000033003300cccccccccccccccc000000000000000000000000cc00cc0111111111111111100000000000000001100110011001100cccccccccccccc000000000000000000cccccccccccccc0333333333333333300000000000000003333333332323232444444444444444400000000000000004444444444440000000333300003333000000000000000000003333000032320c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0000000000000000000000000000000003332333233323332cc00cc00cc00cccc0000000000000000cc00cc00cc00cc0000000003300330000000000000000000000000033003300cccccccc00cc00cc0000000000000000cccccccc00cc000333333330000333300000000000000003333333300002222
|0,5=>0x4040404040404040000000000000000040404040000000223322332233223300000000000000002222222222222222ccccccccccccc8c80000000000000000ccccccccccccc8c803300330033003300000000000000003300330033003300cccccccc444444440000000000000000cccccccc0000000000000003333333300000000000000000000000022222222cc88cc88cc88cc880000000000000000cc88cc88cc88cc8b30033003300330000000000000000000000000000000000cc88cc88cc88cc880000000000000000888888888888888911111111111111100000000000000000000000000000000cccccccccccc44440000000000000000cccccccccccc000000000000000333300000000000000000000000000000000888888888888cccc0000000000000000888888888888888b3333333333333330000000000000000332233223322332200000000000000cc0000000000000000000000000000000000000000000111100000000000000000000000000000000
|0,6=>0xcc44cc44cc44cc440000000000000000cc00cc00cc00cc000000000333333330000000000000000000000000000000000880088008800880000000000000000888888888888888b330333033303330000000000000000030303030303030300000000044444444000000000000000000000000000000033333333003300330000000000000000000000000000000000440044004400440000000000000000000000000000000003300330033003300000000000000000033003300000000cccccccccccccccc0000000000000000cccccccccccccc0000000000000000000000000000000003300330033003300cccccccccccccccc0000000000000000cccccccccc00cc0330133013301330100000000000000003300330033003300
|_,_=>0
def sP:Nat→Nat
|0=>0x148cb801e0c08d0c642901404d86440c8013a182834201005067cb8d0c60501361818c02782830404e86207009b0c0c08034141901c347830200c853028b800c40b01003ca9002503032604005060808d240c1010044190022c7830438686063008b0a0850100244010e182840608080
|1=>0x1a18283205c686620c40136182ab060808d1e4050100c0283040400f0608686401419002017851808501360062c1404005060809b00181ae020030520040065a141ac02003052a4008d0ca880a020148506400a80c14801009d30520280801e941901a1920506840800a2010a026c310
|2=>0x80046860a280800cfc2837c040060a0d7011a3c31014f40060a8480a0080290020033c0a605010018290140400f443010a0201d830404006760dd011a1829014013b90a0c8010ce02831804d800a4050100dc29014040350a0da011a18283420400f0a0c6010ccc2832004a060a0d901
|3=>0xa4051702025052a0c8010ccc283045c08d0c1480a88040060b24a900234305202809b009c2833e046860a0e401001828318046c70a400800d18283200468f540c101003c28320043450a40544020078386343420a0c401003c28382046860af880a020078320045860a0c6010015d83
|4=>0x1e14a8318046860a405011a3e50556548011a1829014040270aec1900234305a20c8011a182aa2029181003c2a12028686401418c02002a1044050100141900234305a040501003e7ce064008d0c1410a2e04686984050d0c802cd145c686981418c02347851040501003c283023434b
|5=>0xac0c4010018283420808d0c1420320046860b2080a0200305064008d0d1c29014040066c14190023430563541900234305202808094141900234786a840517009c295064008d1e1a682145c686202a9011b282901434786401418c0234305a80c8011b4c30520280800ce42822028080
|6=>0xd58190026c0060a0f08202343050640086661480ac0040060a40501001af852028080bc16e8320040060a0880a020079014040110a0c1010018290145ee0d0c8480a0200283b6046860a4050101682901564b8d1e14602140468f0a405171b5c80a465c0060a0c11702343030404686
|7=>0x1a1b205c20880a0234305202a91702343052028b811a3c3050640b811a1828220280800c1480ab20468f0a0c8011a182d62028b8d0c9c290145c08d0d5880a46040060b6c80a0234305202808d0d3028320040060aec602140468fc60c8011a18290157068610085010018295064008d
|8=>0x1e1880a023434b0a0c08d0d082a1202808d1e18290154808d0c1480a03a0305202808dbc18282202808d1e1819002343059e405011a182e7202ac971a1828c042808d0c1509014046860a0c1011a1829014046860b9880a0234305ca405171a1ac101404686b41411014046869e40501
|9=>0xb03080a0234305202808d1e1828320046860a405011a182cf202808d0c17502202808d1e18290145c08d0c1480ac43434f202b5811a18290145c08d0d3028320046860b5080a0234786d4ac1900234305202808dd214610140400506400800c1480a026c0060a405011b5c290145c08d
|10=>0x202808d0c1480a2e046860a405011a1938520280e21a182cd202808d0c1480a0234305
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8deb1b76362c6ad8d2b19f6332c64d8c6b1876302c5ed8bab16f62d2c58d8aeb15762a2c52d8a2b13f6272c4cd896b1276242c46d88ab10f6212c40d87eb0f761e2c3ad872b0e051b4c35186730c86184c2f185b30b06154c29184f30986124c231843a88160f6c1d5837b0696
|6,0=>0x6eeedc1db5336376b8ed599a7bb496686ccf599bb3316656cc9598f3b177624ac2dd82b2ff65f2cbc9d75bae475baeb59d67bac87584caedd5ab2ae7550ca85d4d3a937518ea15d3f3a7774e0e9a5d313a5b74a8e935d233a415474e8cdd16b226743ee8659093a0c640ae7fd8fc39f173d4e78dcee39d57
|6,1=>0x1cf3b986722ee315c2bb7e7
|7,0=>0x4d5899cf321a60bcb98964f2ade523c9e6930d249a45bc8568fcf1dde38b46988c4f171a2abc4e788ef101e1cbc327856f095a0f3c177822d029e01bbfc77e90fb21f243dd77acef3dde43bc17774eecddd63ba57
|8,0=>0x28dbd147a1af419e7fbcf879e2f3ada723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 108 190 0x3fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc151a198415144102430c352e1b02151a56061514412015144102154617000506150605144100151a19021b206d00151a19561420292029201520290c15005406151441001620291a191e0f10171815461420290cd9005e021506160c1500150c3520151441561410142029181500150c352015000502152029181504030016
|1=>0x2e1b0215061620291a190215021b061520290c150241021520150c5d2e1b02154207203d0616144106161441026e00150c150c352015061520191441a41b023d0c150615144100161a195614061914410c15203d20290c411a1904190c3520150c3502160c15073d021614412e4302154207203d0c152e4302150c1520191441
|2=>0x2ed00160d3d02161a19060114410c150c3520150ced00161a1920290c3520152f630214021518150c411a19202921590c161a19203e0c1502150219201920150c1502150d6102140215000514410215201514410c162015004114411a19144120155617061904010c3520150c560615144192140605144107590c1614410c35
|3=>0x2190c412015203d0c151441201584160243b216021902140215203e0c1502162015020a201502092015021502150c15144102150c35201502190c150c1614410215021b0c16021500051a1921590c162e43021500161a191441201920150c15921506051441c53d021702162015144100151a191441202920151a5606151441
|4=>0x215021b02170241021420190c1514410216201620150c15033d02160217021603590c162e4302150616144120160c15061914410d6302140c411a191a19144100151a190d61021402150c158415024314410243203d0c15023d0c151b6102140d3d021620150c1502161441181620190215
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x2200000000000000000044000000000000000000100000000000000000000000000
|5,0=>0x1398000000252119000000000010900000001e30d98684000191000000030200000005c4000000000000000016100004cc0000000000000242000000044400000000000001c60000688000000000060800000000005880001240630210000000000
|6,0=>0x629b0c9806be20002ecd724b63599ac0d5a6aa3539a90d4449f34e1a6892e6943489a3c91a48a343980010868133f19f08f267633999c0cdc46c23511a08ca66232f99748b640002c195c4ac253328180009a64a3241114c8644031f10ecc7063531918c085a62a3
|6,1=>0x1a66d03669b28d922c81
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fd27d93e49ee4f527993c49de4ed27593a85d04e627213889c04de26e13689b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x438c01020003abc00ea7003a8c00e25002a0c00a010019bc0066700188400402000c20002e3000a8c0021800082000108000400000a00002000004600010800028000080000100000200000400000c0000200000400000
|1=>0xf89c03e2500f88c03e2100f80c03a0000d89c0362500d09c0340e00b89c02e2500b88402800009a940262500909c02409008a140220000809002008007a8401e2f00788c016a700598c0163d00589c0142300488001200
|2=>0x2000a08002020003070008043ebc106ef03588c0d22003199c0c26202f0840b42702c0900ac080258a8096270250b40922002191c0862e02189c082620200900802102001407a8301b88c06a00017a8c0566301018803ea3
|3=>0x2006a780080101000401805000a1400281000814000850000120f8948262f
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x400000000008000000000200000000000000
|5,0=>0x28000070e000001c000011e0800d00002000014000000000500040090000100002c00000007800c0000016000000a0050f1000000
|6,0=>0x7a5066876820cb387008ae519e70d4d4730f21357e31fb707494c600ce25e1e965771c38c0e1e766901d500237425a9401b62405561226b55e47578c2e
|7,0=>0x587cf9cba529753c2e7523ea8c18d69785cd9808dbc2af0dc23692ddc589269c051513556f811bd
|8,0=>0x1fb37cd5f16a06dfa7
|9,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_148 4 roots_148 ops++addP pm 2 dom_180 5 roots_180 ops++addP pm 3 dom_184 5 roots_184 ops++addP pm 4 dom_57 5 roots_57 ops++addP pm 5 dom_188 7 roots_188 ops++addP pm 6 dom_156 5 roots_156 ops++addP pm 7 dom_141 5 roots_141 ops++addP pm 8 dom_153 5 roots_153 ops++addP pm 9 dom_157 7 roots_157 ops++addP pm 10 dom_173 8 roots_173 ops++addP pm 11 dom_149 5 roots_149 ops++addP pm 12 dom_61 6 roots_61 ops++addP pm 13 dom_181 6 roots_181 ops++addP pm 14 dom_29 4 roots_29 ops++addP pm 15 dom_60 4 roots_60 ops++addP pm 16 dom_169 7 roots_169 ops++addP pm 17 dom_137 4 roots_137 ops++addP pm 18 dom_168 4 roots_168 ops++addP pm 19 dom_177 5 roots_177 ops++addP pm 20 dom_45 5 roots_45 ops++addP pm 21 dom_172 5 roots_172 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_189 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_172 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_185 8 s (0,roots_185.map (·&&&dom_185)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_189 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_185 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_189==dom_189)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_189 gM v ys):RunD true dom_189 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_189 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_189 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_190
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,36),(4,132),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(12,14),(12,28),(12,44),(12,140),(16,20),(16,144),(18,22),(18,26),(18,50),(18,146),(24,26),(24,28),(24,56),(24,152),(32,34),(32,36),(32,40),(32,160),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc7549
|7,0=>0xb27668862485897833ba0724b
|8,0=>0xe260976607
|9,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x15401540154015400000000000000000110011001100112aaaaaaaaaaaaaaa80000000000000002aa22aa22aa22aa2444444444444444400000000000000004444444444444444aa00aa00aa00aa000000000000000000aa00aa00aa00aa01555555555555555400000000000000000000000000000002aaaaaaa8000000000000000000000002aaaaaaa80000000555500005555000000000000000000005555000055550000aa88aa88aa88aa880000000000000000aa88aa88aa88aa8955555555555555540000000000000001540154015401540282828282828282800000000000000002828282828282828555555555555555500000000000000004444444444444444
|_,_=>0
def sP:Nat→Nat
|0=>0x5471865437186542718654718a654971865427108543710654927186543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5739c68
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1e17641f864d97861976619784a1765e1865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffe36fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x38467
|8,0=>0x52
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_188 7 roots_188 ops++addP pm 2 dom_182 7 roots_182 ops++addP pm 3 dom_62 7 roots_62 ops++addP pm 4 dom_158 8 roots_158 ops++addP pm 5 dom_174 8 roots_174 ops++addP pm 6 dom_54 4 roots_54 ops++addP pm 7 dom_60 4 roots_60 ops++addP pm 8 dom_180 5 roots_180 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_180 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_190==dom_190)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c08000000000c080c00
def gsh_217_2:=0x3030303000000000303030300000000030303020000000003020300
theorem lowS_zo_217_2_81:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3000300000000000300030000000000030003000000000003000300,0,8),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,10),(8,72),(8,136),(16,17),(16,80),(16,144),(18,19),(18,26),(18,82),(18,146),(24,25),(24,26),(24,88),(24,152),(64,65),(64,72),(64,80),(66,67),(66,74),(66,82),(66,194),(128,129),(128,130),(128,136),(128,144),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x6bc2f0af55
|8,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x4040404000000000404040400000000040404040000000004040404c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ea0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2cc88b1722c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_211 7 roots_211 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_203 7 roots_203 ops++addP pm 4 dom_217 6 roots_217 ops++addP pm 5 dom_218 6 roots_218 ops++addP pm 6 dzo_217_2 6 roots_217 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_217_2_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_211 7 s (0,roots_211.map (·&&&dom_211)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_211 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_219 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_219 roots_219 goal_219 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_219
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=S_219.noCircuit
theorem lowS_221:Lower true dom_221 roots_221 goal_221 8:=lower_slice_b [(0x33333333000000000000000000000000333333330000000000000000,1,65)] (by decide +kernel) lowS_157
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_slice_b [(0x55555555000000000000000000000000555555550000000000000000,4,68)] (by decide +kernel) lowS_158
theorem lowS_231:Lower true dom_231 roots_231 goal_231 8:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,32,36)] (by decide +kernel) lowS_233
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_slice_b [(0x505000005050000050500000505000005050000050500000505000005050,32,36)] (by decide +kernel) lowS_234
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_slice_b [(0x505000005050000050500000505000005050000050500000505000005050000,64,80)] (by decide +kernel) lowS_234
def isoMvS_207:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_111
def isoMvS_235:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_187
def isoMvS_243:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_123
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 8:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_123
def isoMvS_249:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_189
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_125
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_123
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005555000000000000000000005554000054500000
def gsh_174_16:=0x55550000555500000000000000000000555400005450
theorem lowS_zo_174_16_42:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x50500000505000000000000000000000505000005050,0,4),(0x55550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa
theorem lowS_zo_175_16_42:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(6,14),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,10),(8,40),(8,136),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,146),(24,25),(24,26),(24,28),(24,56),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
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
|5,0=>0xbc21ca5cf1916fd8217b71d2865ba15b4c34f2934bf412f96701a4d00fdb
|6,0=>0xfef37fc8e4fc66ffc630fab63f62c6f5838ea416e529bdd565d3b16d0b13cba03c83acc4929bec4fbaf37bae1cbab81b085caf061a9387a09139fe869ee4f9d2c99527686e53850368436a7e9dd7c3ac7a20e74db76d88668bcd649b5643be5d84959f8d533055139550be54fee54852546172435473b31d34c04328a93103f21e221f33c1dca11a9ab17a1c1760516b781610614146128a011b0e0d9230d30d0ae5d09d500799406d4d050e3
|7,0=>0xa44bda2b49a2350a2324a0f3a9fd7e9fac89f3969ea4e9dbd69d2c99c3f89c0599a4ab9a4759a0a79822b97b299747292d159197b8e2028d1678b8fd8b2b18b2888aedc8a4f68665085cc3850368440d8320e81e598199f808b97e9dd7d1e77c3487bfa47bb9c7b6cf7a5bd7872d76ec576e4b75c8e759c074f5e74cc274c2e723f9715d2708a16fe176f32668ede684306822965e1f65125647316426263d8c62dfe61fd75bcd15b46a5b0f85a0b955f9e55e4054ee554a0b52bbe51a08516b850448502204e2334e0434d5364836645d6a454894513d406d63e5cb3e26d39425375cd34864344673356932dcc31d703194028eaf289a5285192706225ecb2398021ad01dca11d42b1a20e18f66184d911e321175b112bf0f3cf0ed450d9120cad10b10d0ae5d0a9930a68709c2809be3092e50929b0821603632033ae026eb
|7,1=>0xffc36ffb8bfe11dfaf95fa3c6f83dbf83a6f80f7f6c2ff5845f4d94f417af3ee5f3ccaf201bf1d82f0ed6f0dceeee21ee1c6ea5d7ea00ee96d1e8151e7945e130ae0f36e04afdf4ccdd4d7dccd6db53ad9576d8bd8d8ae2d6ea5d3c6cd2e2dd29d8d1701d0fe0d0855cba4ecba42cabf6c7bb5c74a1c5030c418cc2fcec0feabf24cbeb5abe4b2bd9ecbd5e1bb7b4baf37b89acb6cf6b3f7ab2928b117ab0a70b0595afd73abf40aaefca9872a9292a85a9a80b9a4aa1
|8,0=>0x935ea9125a8d3468aca18aaeb89d598991288ef68832386e5d854b98404383c4382767814927ed157e9dd7cd877c68a7c3487c1ba7911178d6c772117702976d5676b8773fd97250c724c971d3d6fe9a6fbf16ef4e6c4996b6506b1f06a52d6964f6819567a78653b364e5f62661606115fb045f8745ea715e7865c0095bfbc5bd275bcd1595545927258500582da57af656c635532954ee553f2252419520b5516cf5122b4f59b4dcb74cf8b4c2684a23c49c2747bf2479d94513d40a1a402083f08f3edf33e65a3e2563d6513ba1d3b6213a745339a13374a32dcc305052f2e32e0f52e02d2cc582c77e2aba9291b02612c24a3824512224311fee01d42b1c6a4199fc1876516e2216b03166c513740126fa100c00fb4e0e4a60c82d0c6c90c2a70bba20a9700a08a09fce09e4a092e5092d4076c906855064a404c1a00a6b
|8,1=>0xff388fe268fb1a9fa71ff9fa6f9d0bf9a95f952cf6044f5bb7f5b39f45f7f347ef3472f19a0ee676edb05ece7deb050e9c25e7c18e6d14e618fe241ce1808e0b6dded07db77cdb499db132dab28da693da23bd9414d8daed89e4d4b07d270cd181ace945cd738ccb54cc368cb211ca05bc8cfbc828ac7b2fc1bc3c175abf446be3bdbde71bd6d4bc678b7fa7b6b25b56f2b4ea4b49b2b357eb2401b0a70b07d3af5d6aec5aae836ae272ac878a9f28a95daa85a9a8137a47dea1e4ba0f3a9fc7c9f40f9f3969eeb79c73a9a3fa998c897e7997926961ca9529b93ba3
|9,0=>0xfd834f5794eded9e856ee7a39e1ddbe0b7ddf384da0afd7786d5f94d5cb4d34dfd2f3cd2c0cd22a4d092dcffd7cb2b5c7946bfa90bd6d4b9364b68afb2c59b207eaa6d9a7647a3967a148d9f396978929724c96ce59377392b4a8aec389cd084d1c81b4071c8c7003e6d62b664a76135e6109b5f367541ae53785526dc4f9644eb564c9ff4c4cb4ba964b0d44a160430a140a5d39aea2efb32eb272096a2038f1ff421a2bd16b3f0ff790d9b60d4c40bd9a09a56092e503a23
|10,0=>0xe03e0c84bec4e91af5c96f1d76d589644614f6342eaa62e0371deb5
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffff00ff000000000000000000ffffffffff00ff0000ff00ff00ff00ff000000000000000000ff00ffff00ff0000000000000000000000000000000000ffffffffffff0000ffffffff000000000000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000ff00ff00ff00ff00cccccccccccccccc0000000000000000cccccccccccccccc0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffaaffaaffaaffaa0000000000000000ffaaffaaaaaaaaaa333333333333333300000000000000003333333333003300ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffff0000000000000000ffffffffff00ff00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa003300330033003300000000000000000033003333003300ffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffff00ffffff000000000000000000ffffff00ffff0000ffffffffffffff000000000000000000ffffffffffff0000f0f0fff0f0f0fff00000000000000000f0f0fff0f0f0fff000ff00ff00ff00ff000000000000000000ff00ff000000000000000000000000000000000000000000000000ff00ff000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f00ffffffffffffffff0000000000000000ffffff00ffffff00555555555555555500000000000000005555555555555500003300330033003300000000000000000033003300000000000000003333333300000000000000000000000033003300ffffffffffffffff0000000000000000ffffffffffff0000ff00ff00ff00ff000000000000000000ff00ff0000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ffffffffffffffff0000000000000000ffffffff00000000fff0fff0fff0fff00000000000000000fff0fff0f0f0f0f0ffccffccffccffcc0000000000000000ffccffcccccccccc
|0,2=>0xffffffffffffffff0000000000000000ff00ff00ffff0000ffffffffffff00000000000000000000ff00ff00ff0000000f0f03030f0f030300000000000000000f0f03030f0f0300ffffffffffffffff0000000000000000ff00ff00ff00000000ff00ff00ff00ff000000000000000000000000ff00ff00333333333333333300000000000000003333333333333300ff00ff00ff00ff000000000000000000ff00ff00ff000000ffffffffff00ff000000000000000000ffffffffff000000000000ff000000ff000000000000000000000000ff00ff000f0f000f0f0f000f00000000000000000f0f000f0f0f0000000000000000ffff000000000000000000ff00ff00000000555511115555111100000000000000005555111155551100ffffffffffffffff000000000000000000000000ff00ff00ffffffffffff0000000000000000000000000000ff00000000000000000000000000000000000000ffffffff00ff000000000000ffffffff000000000000000000000000ff00ff00
|0,3=>0xff000000ff0000000000000000000000ff000000ff00ffffffff0000ff000000000000000000ffffffff0000ff0000000000000000000000000000000000ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffff00ffffffffffffffff0000000000000000ffff0000ffff0000ffffffffffffff000000000000000000ffffffffffffff0000ff00ff00ff0000000000000000000000ff00ff00ff0000ffffffffffffffff000000000000000000ff00ff00ff0000ffffffffff0000000000000000000000ffffffffff00ff00ff000000ff0000000000000000000000ff000000ff00ff000000ffff0000ffff00000000000000000000ffff000000000000ffff0000ffff00000000000000000000ff000000ff00ff00ff00ff0000000000000000000000ff00ff00ff000000000f000f000f000f0000000000000000000f000f0f0f000000ff00ff00ff00ff000000000000000000ff0000ffffff00ff00ff00ff0000000000000000000000ff00ff00ffff0000
|0,4=>0x3333000033330000000000000000000033330000330000000000ff00ff00000000000000000000000000ff00ff00ffffffff00ff00ff0000000000000000ffffff0000ff00000000000000000000000000000000000000000000ffffff00ffffffffffffffff000000000000000000000000ffffff0000ff00ff00ff00ff000000000000000000ff00ff00ff0000ffffffffffff00ff0000000000000000ffffff00ffff0000ffffff00ffffff000000000000000000ffffff00ffffff00ffff3333ffff33330000000000000000ffff3333ffff3300ffffffffffff00000000000000000000ffffffffff00000000ff00ff00ff0000000000000000000000ff00ffffff00000000ffff0000ff0000000000000000000000ffff0000ff00ffff00ffffff00ff0000000000000000ffff00ffffff0000ffff00ffffff00ff0000000000000000ffff00ff000000000000ffff0000ffff00000000000000000000ffff0000ff0000000000ffffffff000000000000000000000000ffffff00
|0,5=>0xff00ff00ff00ff000000000000000000ff000000ff00000000ff00ff00ffff00000000000000000000ff00ff00ffff00ffffffff000000000000000000000000ffffffffff00ff00ffffffffffff00000000000000000000ffffffffffffff0000ff000000ff0000000000000000000000ff0000ffff0000ffffffff00ff00000000000000000000ffffffffffff00000000000000000000000000000000000000ff00ff00ff000000000000ffffffff000000000000000000000000ffff00000000ff000000ffff00000000000000000000ff000000ff000000ffff0000ffff00000000000000000000ffffff00ff00ff00ff00ffffffff0000000000000000ff00ff00ffffff00ff00ff00ff00ffff0000000000000000ff00ff000000000000ff00ff00ffffff000000000000000000ff00ff000000000000000000ff00ff00000000000000000000000000ff0000ffffffff00ff00ff0000000000000000ffffffff00ff0000ffff0000ffffffff0000000000000000ffff0000ffffff00
|0,6=>0xffffffffffff0000000000000000000000ff00ff00ff0000ffffffffffffffff0000000000000000ffffffffff000000ffffffffffffffff0000000000000000ff000000ff00ff0000000000ff00ffff000000000000000000000000ff00ff00ffffffffffff00000000000000000000ffffffff00ff0000ffffffff0000ffff0000000000000000ffffffff0000ff0000ff00ff000000ff000000000000000000ff00ff0000000000ff00ff00ff00ff000000000000000000ff00ffffff000000000000ffffff00000000000000000000000000ffffff00ffffffff000000ff0000000000000000ff00ff0000000000ff00ff00000000000000000000000000ff00ff000000ff00fff0fff0f0f0f0f00000000000000000fff0fff0f0f0fff0ff00ffffff00ffff0000000000000000ff00ffffff00ff00ffff00ffffff00ff0000000000000000ffff00ffff000000ffffffffffffffff0000000000000000ffffffff00ff0000ffffff00ffffff000000000000000000ffffff0000000000
|0,7=>0xffff0000ffff00000000000000000000ffff0000ffffff00ffffffff000000000000000000000000ffffffff0000ff00ffff0000ffffff000000000000000000ffff0000ffffff00000000000000ffff0000000000000000000000000000ff00ffffffff00ff00ff0000000000000000ffff000000ff0000000000000000000000000000000000000000ff000000ff00f0f0f0f0f0f0f0f00000000000000000f0f0fff0f0f0fff0ffffffffffffffff0000000000000000ffffffff0000ff00000000000000000000000000000000000000ffff0000ff00ffffffffffffffff0000000000000000ffff0000ffffff000000ffff0000ffff0000000000000000000000000000ff00f0f0f0f0f0f0fff00000000000000000f0f0f0f0f0f0fff0ffffffffff00ff000000000000000000ffff0000ff000000000000000000ff000000000000000000000000000000ff00ffffffffffffffff00000000000000000000ffff0000ff0000000000000000000000000000000000ff00ff00ff00ff00
|0,8=>0xffff0000ffff00000000000000000000ffffff00ffffff0000000000000000000000000000000000ffffff00ffffff0000000000ffff0000000000000000000000000000ffff0000ffffffff00ff00ff0000000000000000ff00ff0000000000000000ff000000ff0000000000000000000000ff0000000000000000000000000000000000000000ffffffffff00ff00ffff0000ffff00000000000000000000ffffffffffffff00ffffffffffffffff00000000000000000000ff000000ff0000ff00ff00ff00ff000000000000000000ff000000ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x2050d0309021c1b0c0b1302061a000c190b070a03090c0b13030918000c0b1013020800040b0302171600150c0b100a03020512070a0309050d0309020e0504110206000f0b10020800050d04100302050302060e000c0b100a02080f0b070908000503020e0100050d040703090c0b070a0908050407030600050403020100
|1=>0x120b100a0302051213030902220c0b1302060800050d12071303090c190b100a03020512100a0302050b0309020e00150f0b10030200052112130309020f0b1409020800050309020e000512130302060005120b070a03090b0302061c20001e120a030902040c0b07030600040c0b030201000c0b0a1d020600050d04140309
|2=>0x90205120a0309022b0c0b1303022a00120c0b0a0902260c0b0302060e000c0b130902260028120b0a0309020c0b1303020600050d12101303020c0b0a03090227150c0b110a09020f0b030217160005040b110902000c0b0a090226000c0b03020e01000c0b1303180600120b13030902250504110902000c0b130324060005
|3=>0xc0b0a1409020805122f13030902050d1211130902050410030200051213030902250c0b0713090800150c0b070a03090c0b1302062d000504140302060005040b0703090005120b110a09020c0b1309021a00040c0b11020600050d12130302060f120b0a0902080504070309000512110a0902150f0b110902000f120b2c03
|4=>0x120b13030902230c0b13030918000f0b1303020620003a0f120b0a030902050c0a130309023837120b1303090200040c0b13030902000c0b1303020634000f0b0309021c20000c0b130902081b000512132c030902120b0a132e0309020c0b13090232000c0b0a03090231150f0b0703090005040309020e0005040b10030200
|5=>0x200120c0b0a290309020c190b1303020600120c420b0a030902120b0a1303090240051213030206000c0b130309024100120c0b070a0309150c0b1113090200120c0b132c0309020f0c0b0302061c00040c0b0309020e000f0b0a03090240003e120b0a0309023d0f120b130309020c0b0a1303091800050d12131403090205
|6=>0x120b07030900050d0412130309023c0c0b130309020012130309024500040c0b0302061700120c1f0b0a030902120c0b1309022600120b0a030902440c430b0a030902000c0b0309020e0005120b1303020600120c0b13030206000c0b1303020635000f0b130309024000120c0b0a13090208120c1f0a03090228120b130309
|7=>0x120c0b130309024b040c0b0309024a000f120b0a0309021c120b1303090245000c490b0a030902000c430b13030902000f120b13090208000f120b2903090200150f120b0a030902120c0b1303022a00120c0b100a03020c480b0a030206000c470b13030206000f0c0b13030918000512111309020005461213030902000f
|8=>0x21c1b0005120a13030902390f120b0a030902340c480b13030206000c0b130302064100120c0b1309021a000c0b130902081c00040c0b110902000c0b130302064f000c0b070a0309120c430b0a0309020c4d0b0a030902003d120c0b130309020c0b0a030206170005120b1113090200120b130302061600040c0b13030206
|9=>0xc0b0a0302063f000c0b0a0309024a000c0b13030206000c0b1303090256000c0b5513030902000f120b10030200120b1303020620000512135403090200040c0b1303022a00051213030902530012480b0a030902200f510b1303090200050d12130309021b0504140309020012500b1303090200150c0b0713030900050309
|10=>0x1303020600150c0b0a140309025c120b13030902000f0b070309000f12190b0a0309023d040c0b130309020c0b0309024a1b005a12130309020005040b1403090200040b130302061600050b0309021c1b000c0b0a130309023805120a132e0309020c0b13090226000c0b1303020617000512132e0309020c55130309025700
|11=>0x2061700120b1303090240003a0c0b1303020600040b0309021c20000c0b130309024a000c0b0a1303022a001e0c13030902000c0b130309021c00040c0b0a1d0902000c0309025e000c0b1303022a000f0c0b55030902000c0b100a030205120a0309021c0c0b1314090208000f120b0a03090235040c0b1309021a003c0c0b
|12=>0xb1309021a000c0b0a66030902000c0b6413090200120c0b0a0309022b3d0c0b0a13030902120c0b0a0309024a0c0b6313030902000c620b0a0309020005120b0a0309021c040c0b0302061c00150c0b10130302000561121303090200051207130309000504121303090200120c600b0a030902040b1303020620000f0c0b03
|13=>0xc0b29030902000c0b0a0309026900040b13030902400005120a140309020c0b1303090268000f0b100302003a120b0a0309020b0309021c2000040c0b07030900150f0b14030902000f0c0b0309024a00120c0b130309180005120b0713030900120c0b110a09020c0b0a1309021a0005120a130309021c1e1213030902000c
|14=>0x51230130309020005120b0a14030902120c0b136d0309020f0c0b1303022a0005121013030200040c0b14030206000f120b0309024a00050d12130309021c05121303090245000f12480b0a030902120b130309026c00056b1213030902000c190b0a14030902040c0b13090208003d0f0c0b0a0309020c0b0a0302061c0004
|15=>0x540309020005120a13030902590512130309022305120b10130302000512130309025912500b0a130309020c600b0a030902120c0b0a1d09020c0b130302061c000c0b1303090269000f0b130302061600120b0a1303090239056e1213030902003a120b0a130309020f120b11090200150c0b1303020600040c0b1303091800
|16=>0x7130309000f120b0a13030902040c0b1303090200120c430b13030902000c0b130309023800120c190b0a1303090204120b1303090220000c0b1303090271000c0b130309026f00120b132e0309020c0b0a0309022b0f0c0b1309021a000504121303020600040c0b100302000c0b130902261c00120b0a0309021c20120b13
|17=>0x90267000c1f13030902000c0b1329030902000c0b7313030902000f0c190b13030902000c420b1303090200120c0b0a130309023504120c0b13030206000c0309023972000c0b0a0309026700280c0b13030902000f120b1403090200040c0b0a0309023f000c483303090200120c0b1303090223150c0b130309021c000c0b
|18=>0x30206000c0b1365030902003a0c0b0a03090200120c480b0a0309020c1f0b13030902003a040c0b13030902000c0b0a140309020c0b130309024b00120b130309022000120c130309025b000c0b130309027500050c130309024a003c040c0b13030902000c0b0a1303090241000c0b1303090241000c0b1374090200051303
|19=>0x3c0c0b0a130309020078120c0b13030902003c0c0b13030902000f0c480b0a030902000c0b10130302000c0b130309024c000c030902393f000512130309021c000f120b1303090235003a0c33030902000c0b130309027700150c0b1314030902000c500b1303090220003d0c0b13030902000c760b1303090200120c0b13
|20=>0x30902000c0b130309027c000c0b0a130309023900120c0b130309024a000c430b130309020005120b130309021c003a0c0b0a1303090200040b1303090220000c3b130309026700120c480b0a130309020c0b7b1303090200120c0b1336030902000c0b1379090200120c600b130309020005120a130309020c481303090258
|21=>0x50c131d090200120c0b631303090200120c0b11130902000f0c0b13030902410005120b0a13030902120c0b0a0309023f050c0a130309025900040c0b0a1303020600040c0b0a0309021c00050c1303090259000c500b0a1303090200040c0b1303020600040c0b0309021c000c500b1303090200051303090258000f0b14
|22=>0x1303090239003d0f0c0b130309020015040c0b13030902003a0c3b13030902003a0f0c0b0a030902000c130309025b00120b13030902390005121314030902006a0c0b0a13030902006a0c0b13030902003a120b1303090200050c132c030902000c0b0a132e030902000c7d0b0a03090200050d12130309020c0b132e030902
|23=>0x30902400005120b131403090200050c130309026f000f0c483b1303090200053e13030902000c0b0a13030206000c0b0a0309021c000c0b13030206000f12480b1303090200040c0b130309021c000c0b5513030902007e0c0b1303090200050c1309020800050c135f030902003e0c0b0a030902005c0c0b13030902000c3b
|24=>0x1336030902000c600b13030902000f0b0a0309022000120c0b131d090200040f0b130309022000040c0b130309023400780c0b13030902000c480b130309021c000f0c0b130309028000050c130309023800040c0b14030902000c0b0309021c1b000c0b0a130309024000120c7f0b13030902003c0f0c0b13030902000c0b13
|25=>0x30902000c0b11130902000c7d3b1303090200120c0b1309020800150c1303090239000504121303090200120b0a1303090220150c0b130309021b000c0b0a130309021c000c0b130309024a00050c13740902000c0b0a03090244000c0b130309021c00040f0c0b1303020600040f0c0b0309021c00050c1329030902000c0b
|26=>0x7130309000504120b130309020004120c0b1303090200040c0b1303090235000f0b1303090220000c0b1303090252003a0f0c3b13030902000c190b0a0309024e000c190b1303090220003e120b1303090200120c0b13030902810c0b631303090200040c190b1303090200120c0b0a0309021c0c485f030902003a0f120b13
|27=>0xc7f0b1303090200120c0b0a130309021c120c0b1303090241005d120b1303090200050c130309028000120c1f1303090200510c0b1303090200120c0b13290309020015120c0b0a130309023a0c0b70030902000c430b130309021c00120c420b13030902000f0c0b13030206000c0b0a1d0902000f0c0b0309021c00120c0b
|28=>0x2000f120b0a0309020c0b130309028400120c1f0b13030902000c760b130309022300120c0b0a140309020c480b0a0309022000120b1303090244000c0b0a1303090259000f120b0309021c00040c480b0a03090200820c0b1303090200050c0a1303090239000f0c0b0a03090234000512130309021b000c0b130309025900
|29=>0x52000f0c0b1303090234003c120c0b13030902000f0c190b0a03090200150f120b13030902000c0b1309020800120c0b1013030200120c0b130309024c000512130309023900051213330309020005120b130309021b00050c0a132e030902000c0b13030902351b00050c132e03090200120c0b0a13030902340c0b132c0309
|30=>0x20015050c13030902000c0b130309027a000c0b0a1303090220000c0b0a0309024e000c0b130309022000040c0b0a13030902000c13700309028600040c0b1303090200120c0b130309023f000c480b1303090220000f120b130309021c00040c480b1303090200040c0b1303090241000c0b0a85030902000f0c0b13030902
|31=>0xb1333030902003a0c0b13030902000f0c0b0a030902000d0c0b1303090200040f0c0b1303090200050c13700309020015120c0b13030902000c0b130309028000830c0b13030902000c483b13030902000c0b130309021b000c0b0a0309023f000c0b1303090267000c480b0a13030902000c0b1303090272000c870b130309
|32=>0xc0b1303090235003a0f0c0b13030902000f120b13030902000c7d0b1303090200120c0b1314030902000c0b1303090281000f0c0b0a13030902000c0a1303090286000c0b1303090258000c3b0b130309024e00050c0b1370030902000f0c480b1303090200120c0b0a130309020c0b130309023900120c0b130309021c000c
|33=>0x90200050c0b0a13030902000c0b13030902440004120c0b13030902000c0b0a1303090234000c0b1303090234005d0c0b1303090200050c0a13030902000c880b13030902000f0c3b0b1303090200050c130309027200050c4813030902000c0b130309021c003e0c0b13030902000c480b7003090200150c0b130309020012
|34=>0x21b000f0c0b7003090200050c3b13030902000c0b131d09020005120b13030902000c0b1303090235000c0b130309022300050c1303090239000c190b0a1303090200050c1333030902000c190b13030902003a050c1303090200050c130309023f00120c480b13030902000c0b131403090200050d0c130309020005121303
|35=>0xc0b1303090200120c0b13030902000c0b137003090200050c0b1303090200050c13030902000f0c0b13030902000c1303090286000c3b0b13030902000c0b130309023f000c0b0a13030902000c0b130309024e000c480b13030902000c480b0a030902000c0b135f03090200120c0b130309
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x21300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0xfcb87c9c3d6e1e560ef3875dc3a0e1c970e1386edc368e1ad70d33867dc330e19260c630615c2fce17770b8385a5c2c4e15b70aa38535c28ce13f709c384c5c254e123708e38455c21ce1086080b83e9c1e6e0ec7072b8379c1b0c0d170653830dc178e0b66057b82a1c142e09b604a38235c10ce07f703c381c5c0d4e063702e38155c09ce0486
|6,1=>0x21c710ab8839c40ee2007
|7,0=>0x207c101e07ff03f781f7c0f9e07bf03d781e7c0f1e077f03b781d7c0ea1c741039881c840e25c703037a71b940daa06c6e35b81a9c0d2e0688e33c819ab8cb6064b031d818ac0c36060ce2fe817b40bba05cd02de816bb8b3e0590e2c0815c40ac2055102a0814cb8a4605130281813cc09c9c4d50262812d4094a04950242811d408ca0456e2238
|7,1=>0x2fe417d20bd905e482ee417520b9ae5c582dec16dd8b60e5a882d13166dcb27058b82c1c15ee0ae7056b82b2b15760aab054d82a3394fa0a6d052e82934147a0a2ee50f82843940209f104f08274b938609b304d272654130a097504b282554128a093504937245c120e08f8e47482364119208b90454822641115c87b04376217c109e083f04178
|7,2=>0x3f639f920fbae7d583e739f1dcf7f07b783d7c1e9e0f3f079783c839e220f01077883b841da20ec1075973a8c1d260e8307398398c1ca60e4307198388c1c260e0306f98378c1ba60dc4e6da836a31b35cd8ce6bf735bc1abe0d4f069f834c39a420d110681733d399ca0cd6e663832dc194e0c970643831dc18ce0c570623830e398520c1906048
|7,3=>0x83174153a08a103508137405c200e0ff707f38
|8,0=>0x51c428be544f0a1e950bba83a540ee9ff84fb4a7b653cb09dc94eaba736138ce9be84daca6b9d34d099d94ca4a6321309097c84ba425b212c9095c84a9ca531d289093c849a424b21249091b94894a42a1206e8fc747aba3b611cb08dc946a4232e518528bb7459c22ae1147089a9449ba22e1105287b7439c21ae10c5285a8428ca122508108388
|8,1=>0x624430fe586d2c2e86134307a182b2c0c9601cafee17e52bea85f0caf69d7a50bca85e1baeea57632ba985d0c2e69d7250b8a85c142dea16e32b6895b042d5e56a0eb4885a042cde565f0b27858fc2c5a561d0b07757fc2be1d5df2ae7856f4ab5a159d0ac5955e4aace55570aa2954d42a4a15150a83753e3a9d214d72a62952d4294654912a408
|8,2=>0x72ecb9561c992e44871dcb8ce1c552e22870ccb8425c110e0086fc437be5bcd2dde86eb4373a1b8d0dbd96da4b6b21b472d9a96c94362ddb070d7b86b94b5a65ac12d5886a84351e5a7d2d359696c34961a3b0d14968643415d9f92cf57676c339619bb0cd58666c331259772cb386563b29219390c9396454b20a18f50c7286354318a18b32c509
|8,3=>0x7954bc865e312f0f9783c3bfa5deb2eec9771cbb6a5da6eecb87614baea1d650ea997504ba5e5d1f0e86973f439dddcdf0e669
|9,0=>0x89ecc4d6225b1125888ec445262191104887ebc3d261d910e3986d4c34a219510c2885d442c6615310a1884cc424621131081883c4c1be60cf105f882b4c13a208b303d881ac40b26047301a98094402a20032ff987f8c3fa61fc30fd897e843f1e5f7f0fb787d7c3e9e1f3f0f9787c74be1a1efd0f7687b743d965ebb0f5587a64bd121e790f339
|9,1=>0x231d118688becc5d622db116678af4455a229d11468
|10,0=>0x479223b911d488e6bc716237cf1b688d74469a233d11968
|11,0=>0x11ec7
|_,_=>0
def wAt:=mkWire dB 137 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14094484c0c0044c0105230484e0c0b4502512130300113004302d14094484c0c0044c010c0b4105312134484c14094304d120b4484c0c004484c1503c482d0414c484c1213430010c0b44c0114024484c0c0044c010c1f42c5112130300114024484c0409c484d14068484c0409c484d130045009121303001120b4502512130300113004302d130045009121303001
|1=>0xc0b448bb050a04c0113004482d14024484c0c00450090c0b4484d121304c011503c482d0c134500912130484d0c004302d13004302d14034484c0c004304d120b4484c0c004a4010c134544c0c0042853121304c011213c1053121301027121344c010c294544c120b43001120b44c011213030011306810270f004243a0414c484d12130302d12134500d121303001
|2=>0xc004302d12138f00b0f3b4304d0b0041027040cc3c010c13430010f0b44c010c1344c0139004144f0c0b430d91335c482f0c00448d91335c482f0c00410330413c3c010c134cc010513030010c0b43001050a04c010c0b450090c134482d1213030010414c484c1213430010c0b4484d14094484c0c0b4540f12130482d3000414731213c302d14094484c121343001
|3=>0x131c4484f0c198ec4d0c1342c011503c482d130042c511213030011300430a515130482d0c004544c120b430011300448ff0b13830660b0a44c010409c484d0c004302d130045009121303001120b4484c0c0045428120b430011300410270413c3c010c134105312134484c0c00430660b0a44c010c00430fd130042c4e3a00c3c2d0c134f00b040b43029121301403
|4=>0x121345025121303001130042c4d0409c3029130042c190409c3c010c134f00b0f3b42c010c0b4500d12130300105040484d0c004302d0c13450091213030011213414030c004302d040b44c711213c30010514c484c0c004302d1306810270f004304d0b144484c0c0044c014303c2c711213c4c010f0bc30010c134105312134484c0c00410271213430010c0b41027
|5=>0x14034484c0c00410270f004304d1300450091213030011213c653b0c1382c293c00c102d1213430011306810270c0a44c010c0b4500d1213030010c0681027121343001131c4484f0c00530011248830010b134f04f040b43c010c134484f0c134300113004145312130302d0b1c448531213030011503c482d0c134304d1513030010c134482d0c0044c013c09c102d
|6=>0xc0b44d610c3b8f04f040b43029130041027131c4484f0c0044d490f3b8304d0c1345025121303001040cc10271213430011239c144f0c0b4102d0f004304d1233c144c0c0a82c4d0c5243cee0c1342c0112138484c1213430010c0b4482d14024484c0c004302d12138484f0c00430010513c4c010c0b4304d0b0a830011300410270c0a44c013c03c102d12134484d
|7=>0x120b4484c0c004304d120bc300113004f00f040b43c010c1341027040b43c010c134484c120b4300113005742d0c1b4484e0c004304d14024484c0c00430010b0a44c010c1343c013a00c3c2d0c134316d0b14c484c0c004302d12134484c0c06810270f004304d12138484f0c0b56401050ac4c010c0b43001050a04c010c0b50c0f0b1c4484f0c0043001050a04c01
|8=>0x14094482d1213030010c0b45009121303001121b4484e0c004302d124802c4d0c0044c010c0a810270c0a44c011306810270f004304d3c0cc102d1213430010c0a8104f0c0a44c013c09c102d0c0a4a02d0c5f4ec4c0b0043029033f44c010b138e8cf05134144c0c0b4f0270f3b4304d0b0044d490f3b8304d0b0044c0114094484c0c004302d1213c300113004540f
|9=>0x413c302913004484d14024484c0c004304d120b4484c0c004f04f0f3b4304d0b004f00b040b4484d0c0b4500912130300113004500d1213030013c03c102d0c0a4302d1213c300113004307d0b144484c0c004f00f0f3b4304d0b004299f0c4882c4d650344d630c3b82c010a14c484c13004e8030f0b44c010c134544f120b430010c0b4484f1213c1027121343001
|10=>0x409c484d1513c482d0c004484f0500c302d0514c484c0c004302d0b134304d0c0044c010c6384cd5120bc3001051bc484e0c004302d121302c290c0044c011503c484d120b430013a00c3c2d0c13410270413c302913005a84f0c3442c2a1300430660c0a42c2913004302d121303001130045453120b4484c0c004304d14094484c0c00430010f0b44c010c134302a
|11=>0xc0b450251213030010c0b43001050ac4c010c0b4302a1300449200c0042c4d130040cfd0c0042c4e6a13c30d113004301a0f004304d0c004144f13004302d0f0b4304d0c0044c010c134500d1213030010409c484d120b430013c02c102d0f004304d051cc484f0c004302d0c0b4484c0c0044c01360044cd7120bc30013c09c3ced0b00450251213030010c0b4484c
|12=>0xb134144c0c0b46c011213830011213c482d0c00450091213030010c1343001130044c711213c30010b1c4484f0c004e4010513c302d0b0a43001130041033121343001440043c2f0c13415c31300c302d0c004142813004302d0a14c484c0c0044c013c03c3ced0b004302d0409c484d0c004502512134484c0c004484f1300448e70513c302d130046c01121383001
|13=>0xb13410331213430010b14c484c0c0042c8e4e004304e1513c14010c0b4102d0f004304d040bc302913004102f0f004304d03724144e0c0b4302d0c4882c4d0b144484c0c004544c0c3b42c010f3b0304d0b004ec4d0c1342c01123fc30010b138482f0c0044c010409c484d0c004144e0513c302d1300431220b134317d3b1302c011213030010c1343029130042c4e
|14=>0x123f430010b1383ced0c1342c010c1344c010b13450251213030011248830010b1342c4e0513c302d1213c30010c0b4482f0c004304d05134144c0c0b43cef0c1342c01120b4484c0c004302a13004e8030f0b4304d0b23538010c13810271213430011358c30ee0b0043c2d13004304d0b1343001130042c511213030010f0b43c010c134484c0c0044c01670043122
|15=>0x1300410270f004304d12134484f0c0042c810c0a84c010c0b430ee0b004484c0c004304d0b208302a13004144f13004302d1513c482d0c0042c711213c30011213c30010c0b43c2d13004304d0c204302a130042c010c4882c4d0b134300113004ed3b0c1382c011335c482f0c0040de93b1382c011248030010b1344c010c004302d0b13430ee0b004102d0c0a44c01
|16=>0x1213030010513c30010c0b4484c0c004302d0c3442c2a1300430d10b0a84c010f0b430010c134cc0105130302d050a04c010c0b42d390c1384c010500c30010c0b4142813004302d0c0b40cfd0b1384cd5120bc300114034484c0c004102f0f004304d1300430010c0b43001130042c4e050ac4c010c0b410270c0a44c010413c302913004142b13004302d0b204302a
|17=>0xc198ec4d0b004484c0c004302d0570c4c030c0b42c4d0c1342c010c724144e0c0b410270c0a44c010413c30291300410270f004304d0b13430010c134484d1213c30011358430ee0b00431e93b1382c011503c14010c0b4302d3b1302c010c3f44c010b139742d0c7044c030b004144f0c0b4e8030f0b4304d12134482d0c0043c2d0c1342c010f0b44c010c1342c53
|18=>0xc3b42c0103724144e0c0b43c2f13004304d1214c484c0c00410270f004304d0413c3c010c134544c05004302d1335c482f0c00449200c0042c4d0c0a84c010c1340cfd0c0042c4e040cc3c010c13430290b0a84c01123f430010b138484f0c004ec4f0c1342c0139004144f0c0b4484d12130300112138484f0c00430660b0a44c010b1b4484e0c0043ced0c1342c01
|19=>0xc004484d120bc30010c134302a130043cee0c1342c010f0b4304d0b004304e0b0a44c010c0a84c010c3f430010b138fc010c0042c4e13354482f0c00430290b0a44c011213c300113004ec4c0b1342c010f0b430010c134500d1213030010b4e4304e0b004540f120b4300105004144f0c0b4484d0c004302d0c0a8300113004484e120b430010413c302913004544f
|20=>0x13004302d0b0a84c010c134484e0c004302d050ac4c010c0b42c6d1213830011213c300113004102f1213430010c1b4484e0c004302d3b13c2c010b144484c0c00432013b13c2c0115130482d0c004482d0c0044c010f0b44c030c1342c711213c3001123fc30010b13810270f004304d033f44c010b138104f0f004304d14024484c0c004484d0c004302d131c4484f
|21=>0xc134540f0c3b42c0114094484c0c00449220c0042c4d0513c30010c0b4144c0c004302d1213830010c0b4142813004302d050a04c010c0b42c2a0c0044c0133004144c0c0b4304d0c0044c010b1c8484f0c0042c511213030014e004304e12130300113004302a130042c4d0f0bc30010c134142b13004302d1213c30010c1343029130042c4d830b43c030c134144f
|22=>0xb0043c030c1342c4d0b004484e0c0044c010b13831220b1344c010b134144e0c0b520030b13414010c0b4ec4e0b004302a13004304e13004302a13004302913004302e1300c3c010c13430010b138302a130042c4d1213c30010c1343029130042c4d040bc3c010c134293b0c1384c010f3b8304d0b004304d0b0a84c01040b4484d0c0042c2913004304d120b43001
|23=>0x1300c4c010c0b42dc11300c304d0b004144e0c0b4302d0b134484f0c00430fd0b1384c030b13430ed0b004482f0c0043c2d0c13430010c1342d390c138484c0c004fc010b1384c010c134302e1300430ee0b004304e0b0044c030c0b42c4d0c134300113004144f0c0b4484f0c004144c0c0b43c2d0c1344c010c13414030c0b43c010c1344c030c0b4482d0c004ec4f
|24=>0xc0044c030c0b4302d0c134302e0b0042c4e13004304e0b1344c010b134ec4c0b004484e0c0044c030c134302d0b0040cfd0b13830010c0b4482f0c00538010c138144f0c0b42c2913004144c0c0b4ec4d0b004144d0c0b4302d0b13830010b134484c0c00414030c0b430010c0b44c010c0b43c2f0c134484d0c0042c2a130042c2a1300431c1
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1106211000007f50f8600003ba800000001cd000000000000000037a06a50caa18502ea05a3000016442aa00000a0a000000000000988124c000000008a80000000040500000f101c9800000000d5018282c404ea000012181f5000006d000001650248039000000000000000005200000000000002a8005
|6,1=>0x251447a88b4
|7,0=>0x2cc85890af995b42ae854d0a8180002988524ca31942427e64ed09ba133426064b109421244240847108c211442208434c84a000020a840507f180001f483dcc79a0ef41d6800007490e631c4800006f20db31ae834d067a0cc31908314c6118be417a22e505aa0b1415a82a5052a0000142800004ea0994
|7,1=>0x4508891000022040000874d0ca000042a8845106a209440a88050fea1f943ea87c50f6a1e943ca87850eea00003b28758ce921cf3396871d0e1a000037e86f480001b9436a80000d919ae4354869ccd219a2234046710cd89974000064d0c7a18b430e8610c000181300005f50bd197642ea25c8cb7216a4
|7,2=>0x5fe8bed17ba2f615e48bb900002eb35d06b9100002e045b88b6116a22d045988b211629ac1457c6aecd5c1ab445608ab115422a445408a74d4ca000052a8a45146a289450a8a0513ea27944ea89c51371a6a44cc898cd2fa25b44ae8950d28224d34928918c0000000488490111e2000047088d1118222c4
|7,3=>0x31846288c44d86a30940000c1c9821b031
|8,0=>0x7b06f54de91bcf37986f24de31bc337806ef4ddd1bb737686ec4dd71bab37506e94dd11b9f373a4e68dcb9b9437226e38dc59b88370a6e08dbf9b7c36f26dd8db99b7036da6da8db39b6436c26d78dad9b5836aa6d48da79b4c36926d18da19b40367a6ce8d9b9b3436626cb8d959b28364a6c88d8f9b1c3
|8,1=>0x92e7254a491c8f39187224e431c83390071f4e3d1c7738e871c4e371c6b38d07194e311c5f38b87164e2b1c5338a07134e251c4738887104e1f1c3b387070d4e191c2f385870a4e131c2338407074e0d1c1738287044e071c0b38107014e011bff37f86fe4dfb1bf337e06fb4df51be737c86f84def1bdb3
|8,2=>0xaac554cea81d4d3a94751cea21d413a7c74ece9c1d353a6474bce961d293a4c748ce901d1d3a34745ce8a1d113a1c742ce841d053a0473fce7e1cf939ec73cce781cee29d673a0e729ce239be7370e6c9cd639a67340e669cca398e7310e609cbe397672e0e5a9cb2395e72b0e549ca639467280e4e9c9a3
|8,3=>0xb34765ceca1d913b1c762cec41d853b0475fcebe1d793aec75cceb81d6d3ad460002b39d643ac27578ead9d583
|9,0=>0xc365864b0b96152c265844b07960d2c165824b0396052c065804aff95fd2bf657e4afb95f52be657c4af795ed2bd657a4af395e52bc65784aef95dd2bb65764aeb95d52ba65744ae795cd2b965724ae395c52b865704adf95bd2b7656e4adb95b52b6656c4ad795ad2b5656a4ad395a52b465684acf959d2
|9,1=>0x317962d2c5658a4b1396252c465884b0f961d2
|10,0=>0x18ec71d0e391c7038dc71b0e351c6838cc7190e311
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x3480001a00000c8000060000026000011400008200004000001f800009c000048000023000010800008000003a00001c00000d800006000002a000013000009000004000001800000a000004800002000000c0000050000020000008000002000000
|1=>0x43000020bc00103000047c00023c000117000087e00043c00021a00010cc00086000042f00020e0001060000828000412000208000102400081000040500020200010040008000002ea0000b580003fc00017e00007f00003780001b40000d800006b
|2=>0xc3280060fc00305e00180d000a3f800511000287e001432000a0e0005060002828001412000a0600042fc0020fe00106f00083200040fc00205e00102400080c0004030002008000c1c00057700025bc00116e00087f00043780021b40010d6000864
|3=>0x221f80110f400884e00441c00220900110400080b800402000200c001002000800800343f001a0c000c0fc00605e00300000123000090fc00487600243000120800090000040b000202f00100c000803000401200200800100000070fc0030fe00186f
|4=>0x4c9f80262fc01307e00982f004a3f80250fc0128280092ff00495f80245fc01227e00907f00483780240fc01205e00886500441780210fc010838008018003a3f801c1fc00c8f600605c00302c001807000b87e00547f002a1f801505000a0fe00505c
|5=>0x4001b01260bc0920de04903f020e1f81070f408287e04143d02081f80950fc04883802441401200e008d07804603802243f01120f008906804407e021c7f010e1f80841fc04201002043f01020000801fc0400ee02003f0100138080010040000010020
|6=>0xa0a1f85040fc2420fe12103f09001f841d1fc20c0b810543f08282e04140fc20687e10340808181f840c02020487e10243b081213840902020407e10147f080a1f84050702020fe10103f08080604010fc20083810040408003f84000fc20001e100004
|7=>0x220007f00003f60081fb0024dd8000fe200003
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x21c060609002703000200000600000000092801022f03002903000e000000020300000300001f000a0600000a170602000320000a000f0303000000000a0000000225
|7,0=>0x1504001c0006c1001d340d04e24d391012e0080e26b32a0072061c0607ce1100d00a002e04000a96046612032d046a50000291d2330a002b00420a45a7062c1e0e1e122c2a4a090002062faf2b9f0e0c03bc69986f14711c312ba500430e03000409850e32002da224009e02331a4075aa640668a1bf1a88654b12001b00d533
|7,1=>0xc616031c460003066a910ecfa17eba000aa0c7184bbd02120e5655039503700967798c670e127607003d2a920be189134705042b0ebe0649590d060d092ea900002d190263974c3219
|8,0=>0x5b2fc0d36091b531a3db59c8d7cc519c4e803fa4c8e5c8ac81d38658d38817d59248c68bd5c583d1cbdf99bc33d5abce2142d1b52423a8db5159cab139337341d6824e99dec559c86d5ac279e38374928ccbc8392fcd83514e8bd84e385e7f8f4e59c8363339b9d84ec851a2598d4f74d851941dcb917b525144b2cdb490c3c8
|8,1=>0x7c4a35355dc03a7db3aee495c4d5d556ce00d548595139317a9d57a6c5503c51d4339a6e4e4a5593c283db57af84305351bb50973b5f7823a4d9776b5159c23791c887b7c8add39b3e545cc2dfaa922122c84e8350b8226c
|9,0=>0xd84e9251c2b7d1c65ed3b6d3dcd5cbd84ed139d5c99462cb5159d8ddcbcb9251d8c28e8a51d69259614edbdcd5814ed3924eda51d15159b0dc51c84eabd68359d8c2c85e5e5e614e5159
|10,0=>0x174ecd175117db4e4e4ed6
|11,0=>0x17
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 10 roots_190 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_159 9 roots_159 ops++addP pm 3 dom_63 9 roots_63 ops++addP pm 4 dom_175 9 roots_175 ops++addP pm 5 dom_189 10 roots_189 ops++addP pm 6 dom_151 6 roots_151 ops++addP pm 7 dom_182 7 roots_182 ops++addP pm 8 dom_149 5 roots_149 ops++addP pm 9 dom_158 8 roots_158 ops++addP pm 10 dzo_47_16 6 roots_47 ops++addP pm 11 dom_55 5 roots_55 ops++addP pm 12 dom_183 8 roots_183 ops++addP pm 13 dom_143 6 roots_143 ops++addP pm 14 dom_167 6 roots_167 ops++addP pm 15 dom_31 5 roots_31 ops++addP pm 16 dom_157 7 roots_157 ops++addP pm 17 dom_47 6 roots_47 ops++addP pm 18 dom_179 7 roots_179 ops++addP pm 19 dzo_174_16 6 roots_174 ops++addP pm 20 dzo_175_16 7 roots_175 ops++addP pm 21 dom_173 8 roots_173 ops++addP pm 22 dom_165 5 roots_165 ops++addP pm 23 dom_181 6 roots_181 ops++addP pm 24 dzo_171_16 6 roots_171 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_174_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_175_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 10 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_191 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_191 roots_191 goal_191 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_191
theorem lowS_191:Lower true dom_191 roots_191 goal_191 12:=S_191.noCircuit
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000cccccccc00000000ccccccc800000000ccc8cc00
def gsh_221_2:=0x33333333000000003333333300000000333333320000000033323300
theorem lowS_zo_221_2_85:Lower true dzo_221_2 roots_221 gzo_221_2 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc
def gzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00c80000000000c80000
def gsh_213_2:=0x330033000000000033003300000000003300320000000000320000
theorem lowS_zo_213_2_85:Lower true dzo_213_2 roots_213 gzo_213_2 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_2) [(dom_213,2)] (by decide +kernel) (lower_slice_b (T:=gsh_213_2) [(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82),(66,194),(128,129),(128,130),(128,132),(128,136),(128,144),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|9=>3
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x94644451471f14a
|10,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffccffffcccc00000000ffffcccc00000000ffffcccc00000000ffffccccffff000000000000ffff000000000000ffff000000000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6543210965432106854321076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x4211008
|10,0=>0x187
|_,_=>0
def wAt:=mkWire dB 10 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1955358d
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x21441
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 6
def pmP:Nat→Nat
|0=>0x6ff4fe7fc3f800
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0xd4
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 9 roots_222 ops++addP pm 1 dom_159 9 roots_159 ops++addP pm 2 dom_95 9 roots_95 ops++addP pm 3 dom_219 9 roots_219 ops++addP pm 4 dom_221 8 roots_221 ops++addP pm 5 dom_215 8 roots_215 ops++addP pm 6 dom_207 8 roots_207 ops++addP pm 7 dzo_221_2 7 roots_221 ops++addP pm 8 dom_213 6 roots_213 ops++addP pm 9 dzo_213_2 6 roots_213 ops++addP pm 10 dom_205 6 roots_205 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_221_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_213_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_205 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 9 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_223 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_223 roots_223 goal_223 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_223
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=S_223.noCircuit
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_235
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c080c00
def gsh_249_2:=0x303030303030303030303030303030303030303030303020303030303020300
theorem lowS_zo_249_2_81:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x300030003000300030003000300030003000300030003000300030003000300,0,8),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(16,17),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(66,67),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,160),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|8=>2
|9=>3
|10=>2
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xb4ef906009
|9,0=>0xdadb17408449503
|10,0=>0xaeeae77ec8
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a00000000e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ef0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0ec0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e505050504040404050505050404040405050505040404040505050504040404f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6548710b6548710654371096543710b65431065437a10b543a106543210
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x1dc07
|9,0=>0x1d859ce8
|10,0=>0xb2257
|11,0=>0x347
|_,_=>0
def wAt:=mkWire dB 12 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x6761d6361d8759d63a1d6758e8765f6361d
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0x3303
|9,0=>0xa28262
|10,0=>0xd1c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xff7f5f00
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>7
|9,0=>0x3b
|10,0=>0xa
|11,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_123 10 roots_123 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_235 10 roots_235 ops++addP pm 5 dom_250 9 roots_250 ops++addP pm 6 dom_219 9 roots_219 ops++addP pm 7 dzo_249_2 7 roots_249 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_249_2_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 2 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 2 0 = true)
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
theorem lowS_253:Lower true dom_253 roots_253 goal_253 11:=lower_slice_b [(0x3030303030303030303030303030303030303030303030303030303030303030,16,20)] (by decide +kernel) lowS_249
def dzo_252_2:=0x4444444444444444444444444444444444444444444444444444444444444444
def gzo_252_2:=0x4444444444444444444444444444444444444444444444404444444444404400
def gsh_252_2:=0x1111111111111111111111111111111111111111111111101111111111101100
theorem lowS_zo_252_2_84:Lower true dzo_252_2 roots_252 gzo_252_2 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_2) [(dom_252,2)] (by decide +kernel) (lower_slice_b (T:=gsh_252_2) [(0x1100110011001100110011001100110011001100110011001100110011001100,0,8),(0x1111111100000000111111110000000011111111000000001111111100000000,0,32),(0x1111111111111111111111111111111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555500005554000054500000
def gsh_238_16:=0x555500005555000055550000555500005555000055550000555400005450
theorem lowS_zo_238_16_42:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000000000000000000005555000055550000000000000000,0,64),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_174_64:=0x555500005555000000000000000000005555000055550000000000000000
def gzo_174_64:=0x555500005554000000000000000000005554000055500000000000000000
def gsh_174_64:=0x55550000555400000000000000000000555400005550
theorem lowS_zo_174_64_162:Lower true dzo_174_64 roots_174 gzo_174_64 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_64) [(dom_174,64)] (by decide +kernel) (lower_slice_b (T:=gsh_174_64) [(0x50500000505000000000000000000000505000005050,0,4),(0x55000000550000000000000000000000550000005500,0,8)] (by decide +kernel) lowS_162)
def dzo_92_2:=0x444444440000000044444444
def gzo_92_2:=0x444444400000000044404400
def gsh_92_2:=0x111111100000000011101100
theorem lowS_zo_92_2_84:Lower true dzo_92_2 roots_92 gzo_92_2 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_2) [(dom_92,2)] (by decide +kernel) (lower_slice_b (T:=gsh_92_2) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
def dzo_220_2:=0x44444444000000004444444400000000444444440000000044444444
def gzo_220_2:=0x44444444000000004444444400000000444444400000000044404400
def gsh_220_2:=0x11111111000000001111111100000000111111100000000011101100
theorem lowS_zo_220_2_84:Lower true dzo_220_2 roots_220 gzo_220_2 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_2) [(dom_220,2)] (by decide +kernel) (lower_slice_b (T:=gsh_220_2) [(0x11001100000000001100110000000000110011000000000011001100,0,8),(0x11111111000000001111111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_190_64:=0x5555555555555555000000000000000055555555555555550000000000000000
def gzo_190_64:=0x5555555555555554000000000000000055555554555555500000000000000000
def gsh_190_64:=0x555555555555555400000000000000005555555455555550
theorem lowS_zo_190_64_162:Lower true dzo_190_64 roots_190 gzo_190_64 7:=lower_iso_b (d1:=dom_190) (r1:=roots_190) (T1:=gsh_190_64) [(dom_190,64)] (by decide +kernel) (lower_slice_b (T:=gsh_190_64) [(0x505050505050505000000000000000005050505050505050,0,4),(0x550055005500550000000000000000005500550055005500,0,8),(0x555500005555000000000000000000005555000055550000,0,16)] (by decide +kernel) lowS_162)
def dzo_186_64:=0x505050505050505000000000000000005050505050505050000000000000000
def gzo_186_64:=0x505050505050504000000000000000005050504050505000000000000000000
def gsh_186_64:=0x50505050505050400000000000000000505050405050500
theorem lowS_zo_186_64_162:Lower true dzo_186_64 roots_186 gzo_186_64 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_64) [(dom_186,64)] (by decide +kernel) (lower_slice_b (T:=gsh_186_64) [(0x50005000500050000000000000000000500050005000500,0,8),(0x50500000505000000000000000000000505000005050000,0,16)] (by decide +kernel) lowS_162)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050500000504000004000000
def gsh_234_16:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_16_42:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555500005554000054500000
def gsh_110_16:=0x5555000055550000555400005450
theorem lowS_zo_110_16_42:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4),(0x5555000055550000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,36),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(32,160),(48,50),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,80),(66,70),(66,74),(66,82),(66,98),(66,194),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,136),(128,144),(128,160),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|6=>1
|7=>3
|8=>15
|9=>55
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xffaf2
|7,0=>0x35b912a6ad10191
|8,0=>0xf8c6be032cda6e6c826dbaca9a4b66a498260a4650d0a462303ad4c16e1d15d6a0894407144
|9,0=>0xfbfe4e5fdbe4ec5dbf6fd7397d732ed72dfd627bc8e55c4edec2ca0be2b9b5205aba69ab8fca5caa9e6a69bc239abf799f2998457970588ae938ae447fb287879074d5074b6c7418c6fe346c49269ab16902168c0b5acf65123c489e847fab459db40d043bdc02dd962b9902af2e2996e2559c20f5720ef41dea816d83163cb158c30aee70673d05f3b
|10,0=>0xea774d1192a74c9853a07d51a5b02e4ae322224d1a4340a6d4
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a15555555555555555555555555555555555555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82828282828282828282828282828285555555555555555555555555555555555555555555555555555000055550000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00015555555555555555555555555555555555555555555555554141414141414142aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555544444444555555554444444455555555444444445555555544444444aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000155555555111111115555555511111112aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000005500550055005500550055005500550055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a111111111111111111111111111111111111111111111111111111111111111100002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002828000028285555555555555555555555555555555555555555555555550000000000000000
|0,1=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0001555555555555555555555555555555555555555511111111555555551111111000000002aaaa222000000002aaaa222000000002aaaa222000000002aaaa2225555555555555555555555555555555555554444555544445555444455554444aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a1555555555555555555555555555555555555555555555555555555540000000000000002a2a2a2a000000002a2a2a2a000000002a2a2a2a000000002a2a2a2a5555555555555555555555555555555555555555555555554444444444444444222222222222000022222222222200002222222222220000222222222222000044444444404040404444444440404040444444444040404044444444404040400002aaa80002aaa80002aaa80002aaa800022220000222200002222000022225454545454545454545454545454545454545454545454545454545454545454aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa00015555111155551111555511115555111155551111555511115555111155551112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80002aaa80002aaa80005555555555555555555555555555555544444444444444444444444444444444
|0,2=>0x505050504040404050505050404040405050505040404040505050504040404aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8000000015555555400000001555555540000000111111110000000011111111000000000000000000000000000000002aaaaaaaa82828282aaaaaaaa8282828111111111111111111111111111111111111000011110000111100001111000000000000000000000000000000000000aaaa8888aaaa8888aaaa8888aaaa8889555555555555111155555555555511115555555555551111555555555555111000000002aaaaaaa800000002aaaaaaa800000002aaa8000000000002aaa80000505050505050505050505050505050504040404040404040404040404040404aaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a8000155540001111000015554000111100001555400011110000155540001111000000000000000000000000000000002a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a0000000000000000000000000000000055555555555500005555555555550000
|_,_=>0
def sP:Nat→Nat
|0=>0x1034022452c450d08020544b1030801852c40c20131511030804ce2c40d00891524440c200814c2c40c20072052c42830801c838b10d0c224838b1034093ce2c434224814b10d0c200614c2c40c200614b10a0c20081440c20401c61440c2040
|1=>0x2c40c22476852c40c200714b10309924714b1036020073ce2c40c22474c52c40d00891c54911030891c52c40c25c91c52c40c25891c530b1030801cf14b1030801c52c42830801c52c40c25491c52c45034091cf14b10d0801440c20401cf38b
|2=>0xc29491c614b1030891d31511030891ce14b10d0c22452c40c29091e33c52c40c224714b1030a22471522c40d024714b1210c22478052c40c22477c52c40c22477852c40c22471522c40c200714b10309d24715c2c40c22473c52c45022476c5
|3=>0x891c52c4ac30891db3c52c40c22472052c40c200714b1030aa2474ce2c40c2247a452c40c224714b1030a82474c52c40c20073c52c40d00891c59cb1030891c52c450d0891d31521030891c81512c40c22471512c40c202614b1030891c52c4
|4=>0x801c548b1030891c544b1030891cf14b1030891ce14b1030891c52c45030891c52c40d00891c52c40c2b091c814b1140c91c52c45030801e314b1030891ce14b10340224814b10d0c224714b10d0c200814b1034091cf14b10d0891c838b103
|5=>0x52c40c22472052c40c22474c52c40c224714b10d0c224714b103
|_=>0
def sO:Nat→Nat→Nat
|6,0=>7
|7,0=>0x17803e0078
|8,0=>0x8a720dc7b81d1c6c8195c5e715a04f711a43d90d602e709dc1f8
|9,0=>0x24588f623588b62258872615783620587f61f587b25e487721d487321c486f21b396ae1a3866e192962dd8385ee17385ae163856e152952a14284ea13284aa122846a112842a10283ea0f283aa0e2836a0d193260c182e60b182a60a182660918
|10,0=>0xa5228c8a1227d79d626d899625d895624d8
|11,0=>0x29c7
|_,_=>0
def wAt:=mkWire dB 45 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x247491d14343012474b42087421d0c2431d247450d2ca8301247450d087451d0c7491d0c24b1d2474509207c91d1424b1d247452d14b421d1474b092474b1d1424b0124745090c0491d147431d1424509087451d143431d147491d0c74509207c91d142481f142491d2ca85090c0491d
|1=>0x143521f2c2431d0c2452d2c24b1d142491d2c745492c245462c7481f1424b1d14b431d14743420874f09143482f142421d2c2541f0c2531f14b4e2d1474e09147491d2c2454a2c2521d2c2450d0c24e0d147450124745520c24201247450d147421d14b4b1d2c2530b14b4f0b1434b01
|2=>0x50914b431d2474b092c7450d1474309087480f14245090c2491d0c245510c2421d147431d142491d0c7421d142431d1434509147541d0c24f1d143491d1424542087452d1474f1f143510b2c7491d14b421d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x73043004
|8,0=>0x3433132e32b32832532231f31c31931631331030d30a3
|9,0=>0xa32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b24924724524324123f23d23b2392372
|10,0=>0xae1ad1ac1ab1aa1a91a81a71a61a51
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x8874ee00110bddc0022153b800402f670008056ee00100a9dc001200f800024013e0003e74ea00042e9dc0008193b8000f2a770001874ee00030a9dc0004953b800082a770000c54ee00010a9dc0001513b800013a770000254ee00003fddc00005d3b80000b2770000076ee00000addc0000133b8000022770000001800000000c000000007000000000
|1=>0x200164ee04001d9dc0800193b80f00a6770140544ee0280289dc0480533b808c1a2770110354ee0203ca0dc0406953b80802a2770100154ee0200289dc0400113b80520e67700801ecee00e02bddc01a217bb8030026770050156ee00910addc0121149b80202a2770040254ee0080089dc00c057bb80081aa770010156ee00202a9dc0027953b800462b77
|2=>0x40120ef7748001deee90000addd0809593ba001d3a774002564ee80043d9dd0008193ba00013a77200404cfe20080dbdc2000d53b84000aa7704000ccf604111fddc08221dbb81000ba77
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0xc082
|8,0=>0xf21b65d08e2f2e28c98523ddad
|9,0=>0x743250c5152c1ce902776788cb65025359cae4417c1df9b10a09383e2d1c99a867c518dddb04941a4c12599c6731c98b
|10,0=>0xd154c1623d6235110
|11,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 35 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_250 9 roots_250 ops++addP pm 2 dom_234 8 roots_234 ops++addP pm 3 dom_186 8 roots_186 ops++addP pm 4 dom_126 9 roots_126 ops++addP pm 5 dom_252 9 roots_252 ops++addP pm 6 dom_238 9 roots_238 ops++addP pm 7 dom_174 8 roots_174 ops++addP pm 8 dzo_124_2 6 roots_124 ops++addP pm 9 dom_190 10 roots_190 ops++addP pm 10 dom_62 7 roots_62 ops++addP pm 11 dzo_252_2 7 roots_252 ops++addP pm 12 dzo_238_16 7 roots_238 ops++addP pm 13 dom_222 9 roots_222 ops++addP pm 14 dzo_174_64 6 roots_174 ops++addP pm 15 dzo_92_2 5 roots_92 ops++addP pm 16 dzo_220_2 6 roots_220 ops++addP pm 17 dom_94 7 roots_94 ops++addP pm 18 dom_92 5 roots_92 ops++addP pm 19 dom_124 6 roots_124 ops++addP pm 20 dom_206 6 roots_206 ops++addP pm 21 dzo_190_64 7 roots_190 ops++addP pm 22 dom_220 6 roots_220 ops++addP pm 23 dom_248 6 roots_248 ops++addP pm 24 dzo_186_64 6 roots_186 ops++addP pm 25 dom_122 7 roots_122 ops++addP pm 26 dom_158 8 roots_158 ops++addP pm 27 dom_218 6 roots_218 ops++addP pm 28 dom_110 6 roots_110 ops++addP pm 29 dzo_234_16 6 roots_234 ops++addP pm 30 dom_236 6 roots_236 ops++addP pm 31 dom_46 5 roots_46 ops++addP pm 32 dom_42 4 roots_42 ops++addP pm 33 dzo_110_16 6 roots_110 ops++addP pm 34 dom_188 7 roots_188 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_124_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_252_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_238_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_174_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_92_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_220_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_190_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_186_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_234_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_188 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 15 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 55 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 55 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_167_64:=0xff000000ff0000000000000000000000ff000000ff0000000000000000
def gzo_167_64:=0xff000000fe0000000000000000000000fe000000fa0000000000000000
def gsh_167_64:=0xff000000fe0000000000000000000000fe000000fa
theorem lowS_zo_167_64_162:Lower true dzo_167_64 roots_167 gzo_167_64 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_64) [(dom_167,64)] (by decide +kernel) (lower_slice_b (T:=gsh_167_64) [(0xaa000000aa0000000000000000000000aa000000aa,0,1),(0xf0000000f00000000000000000000000f0000000f0,0,4)] (by decide +kernel) lowS_162)
def dzo_117_2:=0xcc00cc00cc00cc00cc00cc00cc00cc
def gzo_117_2:=0xcc00cc00cc00c800cc00cc00c80000
def gsh_117_2:=0x330033003300320033003300320000
theorem lowS_zo_117_2_85:Lower true dzo_117_2 roots_117 gzo_117_2 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_2) [(dom_117,2)] (by decide +kernel) (lower_slice_b (T:=gsh_117_2) [(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_183_64:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
def gzo_183_64:=0xff00ff00ff00fe000000000000000000ff00fe00ff00fa0000000000000000
def gsh_183_64:=0xff00ff00ff00fe000000000000000000ff00fe00ff00fa
theorem lowS_zo_183_64_162:Lower true dzo_183_64 roots_183 gzo_183_64 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_64) [(dom_183,64)] (by decide +kernel) (lower_slice_b (T:=gsh_183_64) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1),(0xf000f000f000f0000000000000000000f000f000f000f0,0,4),(0xff000000ff0000000000000000000000ff000000ff0000,0,16)] (by decide +kernel) lowS_162)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_175_64:=0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def gzo_175_64:=0xffff0000fffe00000000000000000000fffe0000fffa0000000000000000
def gsh_175_64:=0xffff0000fffe00000000000000000000fffe0000fffa
theorem lowS_zo_175_64_162:Lower true dzo_175_64 roots_175 gzo_175_64 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_64) [(dom_175,64)] (by decide +kernel) (lower_slice_b (T:=gsh_175_64) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xff000000ff0000000000000000000000ff000000ff00,0,8)] (by decide +kernel) lowS_162)
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccccccccccccccccccc8ccccccccccc8cc00
def gsh_253_2:=0x3333333333333333333333333333333333333333333333323333333333323300
theorem lowS_zo_253_2_85:Lower true dzo_253_2 roots_253 gzo_253_2 8:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3300330033003300330033003300330033003300330033003300330033003300,0,8),(0x3333333300000000333333330000000033333333000000003333333300000000,0,32),(0x3333333333333333333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def gzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c800cc00cc00c80000
def gsh_245_2:=0x33003300330033003300330033003300330033003300320033003300320000
theorem lowS_zo_245_2_85:Lower true dzo_245_2 roots_245 gzo_245_2 7:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_2) [(dom_245,2)] (by decide +kernel) (lower_slice_b (T:=gsh_245_2) [(0x33003300000000003300330000000000330033000000000033003300000000,0,32),(0x33003300330033003300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefa0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefa
theorem lowS_zo_239_16_42:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccc8ccccccccccc8cc00
def gsh_125_2:=0x33333333333333323333333333323300
theorem lowS_zo_125_2_85:Lower true dzo_125_2 roots_125 gzo_125_2 7:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33003300330033003300330033003300,0,8),(0x33333333000000003333333300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_187_64:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
def gzo_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0f0a0000000000000000
def gsh_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0f0a
theorem lowS_zo_187_64_162:Lower true dzo_187_64 roots_187 gzo_187_64 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_64) [(dom_187,64)] (by decide +kernel) (lower_slice_b (T:=gsh_187_64) [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0,1),(0xf000f000f000f0000000000000000000f000f000f000f00,0,8),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16)] (by decide +kernel) lowS_162)
def dzo_191_64:=0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def gzo_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffffa0000000000000000
def gsh_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffffa
theorem lowS_zo_191_64_162:Lower true dzo_191_64 roots_191 gzo_191_64 8:=lower_iso_b (d1:=dom_191) (r1:=roots_191) (T1:=gsh_191_64) [(dom_191,64)] (by decide +kernel) (lower_slice_b (T:=gsh_191_64) [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,0,1),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,0,8),(0xffff0000ffff00000000000000000000ffff0000ffff0000,0,16)] (by decide +kernel) lowS_162)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_16_42:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>3
|7=>22
|8=>127
|9=>398
|10=>382
|11=>99
|12=>11
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc63c28a9e35f2ce
|7,0=>0xf804ad4598a588da0a1c9d6fd9c02e98c7879bfa729306f0ec6a68658bb254c0a399283356b29afc28e781ffa7116de0e8fc0deed07ff8
|8,0=>0xfde48fdb8afce76fa601f9424f8e26f4dc3f3076f2061f1c22efdaaeec2fee9a8e956ae8547e73f9e6f34e0b99df87cdd9ebdc916d78fcd53c4d478dd36b3d3673d1a75cfe8acdef5ccb07cb76fc93dfc8cd1c50e3c362cc3441c2702c1f78bd649b94a5b8e9bb885db6c17b52dab4acbaebf2adc74ab72da83e3a5471a4f33a424ca412ba2a49a1e789ae3898a05948da8da078b8418b1f08aa85878b4874eb86ee17d2c27a6bc79148788687648b75a9f7529d7489773e5870f3e6df9f6d42f6c56e6981a69158654bf64763602a95f3ee5a5ed5817d565275616e54254523ae515f24ebfa4c3c145fd6441ba4406f3cc9e3b4c9394fa37aab376f0341523320c314a82f8062e25626e1624ffc2422a229241fcad1f9671ecea1c2e61be4c1aac51a089126b8123b00b34d09a76040270287201c42018dc0183700a7b
|9,0=>0x50a76507614f8f74ed064d17d4c2c14b8864b3394b0bd4ade84ad664a8e049d2e4858d47aca46b7746af745edf4594345903450ff44c23443dd443d8443bb43c9a43b62420114060e3eecd3de923d9ff3cd2b3c88e3c6b43c5a83c0523bb3d3b66f3937338d6a38841377de3772336c4536b6f36778364d335edd34ccc34c233466833fc932e0e328ba31033301ea2f9d32eae92e9c12e73a2d6d52ce902cae12c9df2ac6e2aaed299e529873284fa2756a26ca426b49269662677c264d825c8e25567244452285d20fbe20e8d1f8271f4271f0041ecb31ea1d1e93e1dfc71df421dae11bb0f1b9291b1ad1acdc1a6c01a48a18c4e17e921751f171c3164dc15730143881410813e1912c61120c011fae11f3111d4a0f1f40e8a90e54d0e4b90c93308e5a08c8b08c8708a5b080e8075fa07087050f004e58034b80140c00b2f
|9,1=>0xa9e53a9d3ba8e5da6492a63e2a5f36a523aa4ba7a3a5da35cca292da21e0a0af19fb769f1e79ce8a9ce389c6099c6019bc649ba7a9b7f19b3fc9ada19a42999daa993ac990a698caf97861974e3968fa9581d94c4e9441e93f1f9270c921d591bf791b7f90f7a909e79099f90543901238fe138fc7f8e5768e1488d2bb8cb4d8c00c8bcae8b4308b1f08af818881886e9885dd08584383d7383431831c181eea81baa8119880cff7f77a7f73b7dbcb7d84e7d4b77bd5a7bd067bb7a7a17e79a3878e10772f375a9b759bf75492742c673ac773a18734b8733e2731ab72d0b72c0d7242a7089f706576e5796bf626a0ec6705366fd06589e6530663eb2639b6638b76262c625926203a61e146142b609775f2a55e4045d8d85b7fa5b1b75b17a591c45777c5762456c7f569ce54640523af520e151f8251b0c5197151325512b6
|9,2=>0xf722cf6f53f50b3f4af6f3844f34a4f2f0bf1f8df1dcaf0ac2f04dfefd5eee132edf28edeb1ed6b6ed54eed180ed0f1ecf8eeca5eeca49ec977ec94cec59cebfcdebb51eb3d8eaaf8eaacaea41fe92a2e8318e73c9e6a71e6878e6394e5be6e5ad2e5820e558ae46ede45cde329ee3019e2b86e2897e27d7e1d11e1552e11e0e080ae041adfd17df6bfdededde665ddb6edcf9bdcf28dc48adb846db3e8d9d34d941bd9232d84e2d80b0d7b1ed774fd69f3d61aad5894d4f48d4dd2d433fd1516d14dbd0a40d0247cf38dcf2f8ce5a0cdcb9cc87dca636ca475c9852c9599c9112c84e2c83fec7cf5c763ec463ec3882c1a53c1504c13bac101bc0e8abf9fbbf847bf6c6bd1a6bc51ebc0e4bb663bb2a8b9b31b8e49b7fb7b7931b74dab62fcb54cfb4e9bb47ddb442eb3109b255eb1abab07c1aee85aede7acb28ab78aaac1c
|9,3=>0xffec6fe34bfd5e6fd0c8fcb7efcacffc8fffb78afaf4dfa9f2f9d69f99b6f816ef7d48
|10,0=>0x4d1244c6704c0e34aebd4a7724a6764a61349cd14883a4844a471d846fcd4601a44602440ee42f2e42bc341832404d1404be402d8401ec3f4ee3db933cdcb3cc493c8c63c4f63c25f39dad39c823992c38a143861137481365fc347383364a32f9131ad730f403044f2efbe2e7ae2e1ab2d8702d1aa2c96b2b8df2adcf29a91294e8290ea2732f26a6d2539924e802417823d4a2209f215d9211151fe931e49e1d5821ceac1c0e31b6941aee01a16819a371968818c4f187ed17935173161619714fcb13d3613d16129a3128fb126951212611e061176b11477111800ffc90f9df0f6f60f0c80e93a0e36a0d2f00d15f0c60c0c2fb0be020b8c70b63c0b6000b2ed0ac5b0a02d09c39097c308ebb08b8a086b8084b2082320818a07aad07979074c4069bf06564057ac043a503870032970316d02f5402d69028f2025ba0032d
|10,1=>0xab23faaffaaae6da969ca9137a8e84a6f5ca6500a568da4ad0a496fa4721a3dc7a383ba32c3a31eca2847a1e4ba1d56a05d49fcbb9e5cd9d8839cb6b9bb019b8b99b7e89b6729a35899fb7994c298768966d594cf793b15935c59324e92dc2900808f8628e6d08d43d8d1f18c7418c4838c0918aa738a89989ec689a5a8868f87ff8879c0878bb867d7867278604384d43841c183d1e8368280efb80894807dd8060a7f8f47be417b2747b0ea7b07d7adcd7acce799a9791e7770e87706176edd75725733c87277d726226f2ae6ea3b6e5796db416d8866c6016bff96abcc69e6c6984769103677626719c664d265c8d65ad4658de636d86269b6231a622d761fee61c9c60b92601b85fcd65f85c5f54f5ef6a5ec075c1945ba565b7ef5b1025862457ab0570e656de35697d552a953e0e53baa533e54f9244e71a4e6914d741
|10,2=>0xffb58fd40ffcd73fbc1dfafaafa346fa340f9128f7ad3f6bb6f4df3f3e3af204cf1c46f149af13c0ef589ed151ec5f9ec171ebe07eb0a0eace5e71dfe6448e60c7e5cc7e5748e5553e4867e4779e415ee2e40e26c3e1d9ae1a4de157ce1572e06c6e0419def33de425de1f2ddf63dd987dc54cdc032dbe44dbde6db730dafd4dad68d962ed8960d88b9d87d1d86fdd7cf9d719dd69e5d5e3bd4a4bd4822d45cdd42dad41f9d36bbd2ba7d15a0cf7eecf6face739ce023cde9acd77dcd769cc1dacab45cab1dc970ec8d23c8c5ec7f59c6766c6627c5640c52ecc4a87c341ec336fbf680be551bdcfdbd34dbcff6bcde1bcb70bc261bbfbebb014b9d44b90c6b882db7f08b7b2ab7931b664bb65feb5994b49d2b42a1b3a20b3985b35d0b32feb2e3cb2b5db21b8b210bb0cbfb062daebb8ae2e2acc34ac372ac0c0
|11,0=>0xfccb4f939af4ec1f2b24ed252e178ddf1cadd90fdb393da9a6d919bd84f5d6e61d30b0d208dd04d9cf279cb2c7c6bcdc61a2c3153c1b85c1893c17ddbc505ba73cba5abb7cbab4e53b4dcab2e99b08a3ade64ada7fad0a6a863aa7ea4a6f66a5459a4cc5a4803a45aea36dca2b68a2686a052995f75926f792474922908ffae8c0998bcc782b017e9c3782eb7699771b25704516c1cd6b3706afc166b746674c642dc641235e4015a18057fb9578e8540444d52b4d0774cdb14c8e34aaa7457d542b8b3eef2348f5343e12e4f129dba279d8277741f2b11d9861d6121ab971a6ae16d600d86d09e080946307c280699205d8e055e901703
|12,0=>0xfff0bdd9d2c33a39892d8e306795a972a9065c4f61e181939f0c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeaaffffeeeeffffeeaafefefefefefefefefefefefefefefefefefefefefefafefafefefefefefafefa0000fefe0000fefe0000fefe0000fefe0000fefe0000fefa0000fefe0000fefaffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaeeaaeeeeeeeeeeaaeeaa00000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
|0,1=>0xccccccccccccffffccccccccccccffffccccccccccccffffcc00cc00cc00ff000000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffccffffffff33333333ffffffff33333333ffffffff33333333ffffffff33330000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ccccccccccccffffccccccccccccffffccccccccccccffffccccccccccccffcc3333333333333333333333333333333333333333330033003333333333003300fffffefefffffefefffffefefffffefefffffefefffffefafffffefefffffefaffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffffffffff33330000333333333333000033333300ffffffffffffffffffffffffffffffff00000000ffff333300000000ffff3300ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00cccccccccccccccccccccccccccccccccccccccccc00cc00cccccccccc00cc00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
|0,2=>0xffff3333ffff3300ffff3333ffff3300ffff3333ffff3300ffff3333ffff330000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffffffffffffffffffffffffffffffffccccccccffffffccccccccccffffffccffffffffffffffffffffffffffffffff00000000ffffff0000000000ffffff003333333333330000333333333333000033333333333300003333333333330000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff33ff33ff33ff00ff33ff33ff33ff00ff33ff33ff33ff00ff33ff33ff33ff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000333333333333330033333333333333003333333333333300333333333333330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc00000000000000000000000000000000ffffffffccccccccffffffffccccccccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffffffffffffffffffffffffffffffffffff0000ffff3333ffff0000ffff3300ffffffffffffffffffffffffffffffff00000000333333330000000033333300
|0,3=>0xffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc33333300333333003333330033333300333333003333330033333300333333003333333333333333333333333333333333333333333333003333333333333300333333333333333333333333333333333333333333ff33003333333333ff33003333333333333333333333333333333333333333333333333300330033003300ffffffffffff3333ffffffffffff3333ffffffffffff3333ffffffffffff330000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff000000000033333333000000003333333300000000333333330000000033333300ffff0000ffff3333ffff0000ffff3333ffff0000ffff3333ffff0000ffff3300ffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffff00ffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc00000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000000000333333330000000033333333000000003333333300000000330033003333333333003300333333333300330033333333330033003333333333003300
|0,4=>0xffffffffffffffffffffffffffffffff333333003333330033333300333333000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffccffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff3300ffff330000000000ffff333300000000ffff333300000000ffff333300000000ffff3300ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ff00ff000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000003333333333333333333333333333333333333333333333333333333300000000ffffffff33333300ffffffff33333300ffffffff33333300ffffffff333333003333333333333333333333333333333333333300333333003333330033333300ffffffff33333333ffffffff33333333ffffffff33333300ffffffff33333300ccccccccffffffccccccccccffffffccccccccccffffffccccccccccffffffccffffffffffffffccffffffffffffffccffffffffffffffccffffffffffffffcc3333333333333333333333333333333333333333333333333333000033330000ffffffffff33ff33ffffffffff33ff33ffffffffff33ff33ffffffffff33ff00
|0,5=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccc0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0cffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffff33333333ffffffff33333333ffffffff33333333ffffffff33333300ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffccffccffffffffffccffccffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000cc00cc000000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff00ffffffffffff0000ffffffffffff0000ff00ff00ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000033003300330033003300330033003300330033003300330033003300000000ffffffffffffffffffffffffffffffff00000000333333330000000033003300ffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc
|0,6=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc3333333333333333333333333333333333333333333333333333333333003300ffffffff33333333ffffffff33333333ffffffff33333333ffffffff33003300ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffccffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffff003333000033333333333300003333333333330000333333333333000033333300ccccccccffffffffccccccccffffffffccccccccffffffffccccccccffccffccff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff0000000000000000000000000000000000ffffffffffccffccffffffffffccffccccccccccffffffffccccccccffffffffccccccccffffffccccccccccffffffcc000000000000000000000000000000000000000000000000ffffff00ffffff00ffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff00000000000000ffff000000000000ffff000000000000ffff000000000000ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00
|0,7=>0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc0000000033333333000000003333333300000000333333000000000033333300ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff00ff0000000000ffffffff00000000ffffffff00000000ffccffcc00000000ffccffccffffffffffffffffffffffffffffffff33333333333300003333333333330000ffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffcc00000000ffffffff00000000ffffffff00000000ffff000000000000ffff00000000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc000000000000000000000000000000000000ffff0000ffff0000ff000000ff00cccccccccccccccccccccccccccccccccccccccccccccccccccccccccc00cc000000000000000000000000000000000033333333333333003333333333333300ffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc3333333333333333333333333333333333333333333300003333333333330000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff00ff33ff33ff33ff00
|0,8=>0xffffffff33333333ffffffff33333333ffffffff33330000ffffffff333300000000000000000000000000000000000033333333330033003333333333003300ffff0000ffff0000ffff0000ffff0000ffff3333ffff3300ffff3333ffff3300ccccccccffffffffccccccccffffffffccccccccffffccccccccccccffffcccc00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ffffffffffffffffffffffffffffffffff33ff33ff33ff00ff33ff33ff33ff00ffffffff00000000ffffffff00000000ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff003333333300000000333333330000000033333333333333003333333333333300000000000000ffcc000000000000ffcc000000000000ffcc000000000000ffccffffffff0000ffccffffffff0000ffccffffffff0000ffccffffffff0000ffcc0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000000033333333000000003333333300000000330033000000000033003300ffff0000ffff3333ffff0000ffff3333ffff0000ffff3300ffff0000ffff330000000000000000000000000000000000ffffffffffffffffff00ff00ff00ff00ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffff00ffffff00
|0,9=>0x3333333333333333333333333333333300000000333333000000000033333300ff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ff00ff00ffffff003300330033333333330033003333333333003300333333003300330033333300ffffffffffffffffffffffffffffffff33333333333333003333333333333300ffffffffffffffffffffffffffffffffffffffccffffffccffffffccffffffccffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff00000000000000000000000000000000000000000000ffccffcc00000000ffccffcc0000000000000000000000000000000000000000ffffffcc00000000ffffffcc0000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff003333333333333333333333333333333333003300330033003300330033003300ffff3333ffff3333ffff3333ffff3333ffff3300ffff3300ffff3300ffff3300ccccccccccccccccccccccccccccccccffffffffffffffccffffffffffffffcc000000000000000000000000000000000000ffcc0000ffcc0000ffcc0000ffccffffffffffffffffffffffffffffffff0000ffcc0000ffcc0000ffcc0000ffcc00000000000000000000000000000000ffccffccffccffccffccffccffccffcc3333333333333333333333333333333333330000333300003333000033330000
|0,10=>0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffffffffffffffffffffffffffff0000ffff0000ff000000ffff0000ff00000000000000000000000000000000000000000000000000ffccffccffccffccffffffffffffffffffffffffffffffff0000000000000000ffccffccffccffcc0000000000000000000000000000000000000000ffffff0000000000ffffff00ffff3333ffff3333ffff3333ffff3333ffff3333ffff3300ffff3333ffff330000000000000000000000000000000000ffffffffffffffffffffff00ffffff0000000000000000000000000000000000ffffffffffffccccffffffffffffccccffffffffffffffffffffffffffffffffffffffffffffffffffccffccffccffcc00000000000000000000000000000000ffffffffffffffffffccffccffccffccffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffffffffffffffffffffffffffffccffccffffffffffccffccffccffccffffffffffccffccffffffffffccffccffffffccffccffccffffffcc00000000ffffffff00000000ffffffff00000000ffffffff00000000cccccccccccccccccccccccccccccccccccccccccccccccccccccc00cccccccccccccc00
|0,11=>0xffff333300000000ffff333300000000ffff330000000000ffff33000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffffff00ff00ff00ff000000ff00ff00ff0000ffffffffffff3333ffffffffffff3333ffffffffffff3300ffffffffffff33003333333333333333333333333333333333333333333333333333330033333300ffffffffffffffffffffffffffffffffffffffff33333300ffffffff33333300ff33ff33ff33ff33ff33ff33ff33ff33ff33ff00ff33ff00ff33ff00ff33ff00ffff0000ffff0000ffff0000ffff0000ffffffffffffccccffffffffffffcccc000000ff000000cc000000ff000000cc000000ff000000cc000000ff000000ccff00ffffff00ffccff00ffffff00ffccff00ffffff00ffccff00ffffff00ffcc00ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffffff33333333330033003333333333003300ffffffffffffffffffffffffffffffffffff3333ffff3300ffff3333ffff3300ffffffffffffffffffffffffffffffff00000000ffccffcc00000000ffccffcc000000000000000000000000000000000000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff00
|0,12=>0xffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffffffff00ff0000ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff00ff33ff00000000000000000000000000000000000000000000000000ffffffffffff0000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffff000000000000000000000000000000000000ffff3333ffff3300ffff3333ffff330000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff003333333333333333333333333333333333333333333333333333333333330000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffffffffffff0000ffffffffffff00003300330033003300330033003300330033333333333333003333333333333300ffffffffff33ff33ffffffffff33ff33ffffffffff33ff00ffffffffff33ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc0000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff000000000000ffffffff00000000ffffffff00000000ffffcccc00000000ffffcccc00000000000000000000000000000000ffffffffffffffffffffffffffff0000ccccccccccccccccccccccccccccccccccccccccffffffccccccccccffffffcc
|0,13=>0xccffccffccffccffccffccffccffccffccffccccccffccccccffccccccffcccc0000000033333333000000003333333300000000333300000000000033330000ffffffff00000000ffffffff00000000ffffffffffccffccffffffffffccffcc0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ccccffffccccffccccccffffccccffccccccffffccccffccccccffffccccffccffffffffffffffffffffffffffffffffffffffffffffffffffffccccffffcccc0000ffff0000ffff0000ffff0000ffff0000ffcc0000ffcc0000ffcc0000ffcc00ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00000000ffffffcc00000000ffffffcc00000000ffffffcc00000000ffffffcc00000000000000000000000000000000ffffffccffffffccffffffccffffffcc0000ffff0000ffcc0000ffff0000ffcc0000ffff0000ffcc0000ffff0000ffccffff0000ffffffccffff0000ffffffccffff0000ffffffccffff0000ffffffccffffffffffffffffffffffffffffffffffffffffffffffff3333333333330000ffffffffffffffffffffffffffffffffffffffffffffffff333333333300330000000000000000000000000000000000ffffffffffffffffffffffffff00ff00
|0,14=>0xffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff00ccccccccffffffffccccccccffffffffccccccccffccffccccccccccffccffccffffffff0000ffffffffffff0000ffffffffffff0000ff00ffffffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffccccccccffffccccffffccccffffccccffffccccffccccccffccccccffccccccffccffffffff33333333ffffffff33333333ffffffff33003300ffffffff3300330000000000000000000000000000000000333333003333330033333300333333000000333300003300000033330000330000003333000033000000333300003300ccccccccccccccccccccccccccccccccffffffffffffccccffffffffffffccccffccffccffccffccffccffccffccffccffcc0000ffcc0000ffcc0000ffcc000000330033003300000033003300330000003300330033000000330033003300000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff0000000000000000000000000000000000333333333333000033333333333300000033003300330033003300330033003300330000003300000033000000330000ccffccffccffccccccffccffccffccccccffccffccffccccccffccffccffcccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc
|0,15=>0x3333330000000000333333000000000033333300000000003333330000ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc00ff00cc00ff00cc00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00000000333300003333000033330000333300003300000033000000330000003300ffccffccffcc0000ffccffccffcc0000ffccffccffcc0000ffccffccffcc0000ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffff0000ff000000ffff0000ffff0000ffff0000ffff0000ffffffccffffffccffffffccffffffccffff00ffffff00ccffff00ffffff00ccffff00ffffff00ccffff00ffffff00ccccccccccccccccccccccccccccccccccffffffffffccffccffffffffffccffccffffff00cccccc00ffffff00cccccc00ffffff00cccccc00ffffff00cccccc00ccccccccccccccccccccccccccccccccffffffccffffffccffffffccffffffcc000000000000ffff000000000000ffff000000000000ff00000000000000ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x310121e0c0b0f0e0d0313120c1d0b0f0d0310120c0b0e050d0403020c0b1c04031b10120c06050403121a01000b0a05040900070b050409020800070b1905040902000717060b05040302000b0504031012160c0b0504031012150c0b14050403020c06050403131201000b0f0e0d03020c0b0a040908000706050403020100
|1=>0x10120c2827340d031012000b1c0504031012310c0b2f1c040310120c0b0504032d10122c0c0b0e050d040313120c2705290d0310120027050d03101226000b050d03121a250c0b0f050d03020c18230e052203120c0b0f0e0d03121a0c0b2105040310120c0b0504031012200c0b1c0403101f120c17050403020100070b1c04
|2=>0x100280b1c04031012260c0b050d034310120c0b0a050403020007420b050d0310120c170504031312010007400b05040310120c0718240e050d0310120c2a050d0310123f0c2a0b0d0310123e0c06110b050403123d000b050403123c00073a0b05040310120c070b0504031012370c070b3605040310120c070b05350d0403
|3=>0x310120c0b050d031012260c2a050d034d123f000b34040310122c0c110b050d031012250c0b0504034c10120c070b05040310124a0c070b1c04490310120c240b0f1c320310120c18050d031012470c460b050d0310120c280b0504030200070b340d0310122e0c0b0e050d0403121a0c440b1405040310120c060504031012
|4=>0xb1c040310120c170b050403123c00070b050d031012520c0b050d0403123d0c0b0504031012510c240b0e05220d03120c500b0e050d0310120c270f0d0310122b000b1c04034310120c2a0b040310124f0c280b340d0310120c2a1c040310123f0c230b0f05320310120c0b050d0310124e0c17050403121a0100070b05290d
|5=>0x120c070b1c29040310120c0b050403123d00070b1c04031012260c0611050403101201005a0b05040310120c07590b0e05040310120c0b0f050d0313120c0b050d031012570c180b050d031012410c272f050d03101200550b1c040310120c11050403123d0100070b050d0403020c270f540310120018230e05040310120c46
|6=>0x122b0c240b6205040310120c0b0f050d03121a0c0b1c04031012610c0b05040310121e0c07240b1c04031012600c0b050410125e0c07240b0f0e0d0310120c2827050d03101226000b341c04031012330c0b1c040310125c0c0b0f0d0310125b0c0b0f050d0302000718241c052203120c180b1c050403123d0c0b0504031b10
|7=>0xc070b1c0504036710120c2a270d0310123e000b2f050d0310120c17060b050403131200180b05660310120c0718240e052203120c07230b0504031012600c650b0e05040310120c1823052203120c230b0e05220403120c18050403123d0100070b140504036410120c0b0e050d0310123f0c0b1405040313120c0b0f0d0310
|8=>0x1012410c0b14050403121a0c170b0504030200074627050d031012000b0504090200070b056b0d0310120c230b3805040310120c1d0b0f040310120c070b0f0e6a0d0310120c18050d031012010c0b140504030200074227050d031012000b0e050d031012300c0b050403101f120c070b1c32040310122b0c0b050403101268
|9=>0x120c070b1c040310126f0c2a0b1c040310123b0c230b6305040310120c1d0b050d040310120c17060b050403121a00230b0f0e040310120c0b1c050403123d0c280b050d031012260c180b050d03126e0c6d0b1c05040310120c180b050d0310124e0c18050d031012330c0b14040310122b0c110b0f0e0d0310120c0b0f0d03
|10=>0xc070b05040310126e0c070b050d031012530c0b790403101278000750270504034d12000b050d031012770c0b0504031012760c0b0532040310122b0c070b05040375120c070b0504031012740007230b0f05040310120c270504540310120018730522031200070b050d034d123f000b05700403101200070b053204036710
|11=>0x101200070b050d0310122600072a05040310127c0007240b0f0e040310120c07282705040310122600070b79050d034d12000b0f040310127b00070b0f040310125b0c070b0504036710120c070b34040310122c00077a0b1c040310120c0b6905040310120c072a0b0f0d0310120c280b050403121a0007180b0e0522031012
|12=>0xb14056a040310120c11240504034d12000b791c040310120c2a1c040310123f00070b8005040310120c0b050d040313120c0b7f040310122e00070b05040310127e00070b3404031012010007240b6305040310120c072a0b05220d0310120c0b1c0504031012300c28270504034d1012000b057d040310120c070b05290d03
|13=>0x120007060b340403101200070b0f040310122b0c07180b050403123d00070b1c040343101200076d0b0532040310120c077a27050d0403101200180b0e050d0310120c2a0b040310124f0007170b1c05040310120c0b050d0310122e0c0b4b05040310120c070b05220d0358120c280b340d031012000728180b1c040310120c
|14=>0x182714050d031012005027050d031012002a8505040310120007180b0504030200070b0f05810310120c280b050403123d00072a0b0581040310120c0b1c04031012840c0b0f1c320310120c2a0b1c32040310120c0b1405220d034d12005f0b05040310120c070b0e05040310123f0c070b0504032d101200070b8205040310
|15=>0x70b050d034d1277000b0f04038c10120007460b1c040310120007240b0e050d040310120c2a0b05040310123b0c072a0b040310128b0c17110b050403123d0007110b1405040310120c28180504031012010007242705220d0312000b058a0403101200070b050d040310125b0c0b05040310128700070b050d0403123d0007
|16=>0x91031200070b0f050d031312000706180b050d031012008f0b0f0403101200070b050403641012000724270f0504034d12002a27040310123e0007550b1c0403101200070b0f05040364101200070b05040310122c0c0b8d050403101200071824050d0310120c0b050d04030200070b2f05040310120c076d0b05040310120c
|17=>0x280b050d0310120c28060b050d031012001706110b0504031012000b050d040310122b0c940b050403101200070b341c040358120c0b1c050403101292004227050403101200070b0e0504031012300c070b88040310122b0007060b050d0403101200280b7f04031012000718270522034d1200180b34050d0310120c182405
|18=>0x310120c07480b05040310123b070b1c040310122600070b050d04031012470c0b1c0504031012930c2a05040310129900070b050d0403121a0c1105040310120100070b050403101298000727050d03101297002a0b14040310120c0b0504031012310c072a0b05220d034d12002a0b95040310120007480b05220d0310120c
|19=>0xb05040310129f00070b1c040310122e0c0b0f04031012410c070b05040310129d0007180b1c050403123d00074627050403101200070b05040310129c00072427056a040312001824056a031200076c180b050d0310120c2a0b1c22040310120c0b9b1c05040310120c0b1c290403101200070b9a05040310120c070b056b04
|20=>0x280b0504031012260c0718241c05040310120c0b05a29e040310120007180b050403126e0c07180b05040310124e0c077a270504034d12002a27340d04031012000b053204031012a10724270f050d03101200180504031012330c07170b05040310122600071873050d03101200280b050403a012000718241c052203120007
|21=>0x1a0007240b0f05320310120c07270529040310120007280b05040310123d0007270b050d0310123e000b1c0504031012450c0b05a6040310120c2705040310122600072a0b040310124500070b05041012a40c07480b341c040310120c0b05040358101233070b050403121a00071824050d034d12000b0e056a0d040310120c
|22=>0x1012450c0b140504036410120007180b05031012530c07180b341c040310120c0b14050403131200070b050d04031012410c2827340403101200070b0f0d0310122b000717180b050403123d00070b1c0504031012010c270b0f340d031012007a0b050d040310120c0b0504490310120c07a80b05040310120c0b0f050d0312
|23=>0x1200071827056a031012000b050403123d00070b3404031012ab000718230522031200072a0b0f0d034d1012000b140504031012010c240b05220d03120c280b1c040310120c180b14050d0310120c28060b1c04031012000baa05040310120007500b050d0310120c110b0e050d040310120c0ba905040310120c0b14050403
|24=>0x240e05040310120c070b058104031012330c2a05040310123f0c070b1c05040310123b0c0b0522034d12af00182305040310120c170b050403131200070b0504031012390c070b2f050d03101200072a0b040310123e0c070b0581040310123b0c0b1c0504031012ae000b05ac040310120c0baa050403121a00070b0f540310
|25=>0x503101296002805040310120100070b1c04031012600c0b050d034d10122e000b0504034310120c07170b050d040310120c0bb3050403101200072a0504031012b200070b0f0e0d0310120c281827050d03101200710b040310123e00070b1c0504031012330c0b050403020007180504031012010007b00b05040310120c18
|26=>0x40310120007590b05040310120c2a27140d0403101200171105040310120100072a273404034d12000b0e05220d0310120c27050d03101230000618270504031012000b050d031012970c27050d040310120100110b0522034d120018050d031012010007b80b05040310120c0b0f05b603101200070b1c04031012b50c1827
|27=>0x1200240b1c05220403120c0b050d0310123e0c0b14050403121a0007500b1c05040310120c180504031012470c07730b05220d031200270b79050d03101200460b05040310120c070b04031012902e00070b6205040310120c0b34040310122e0c072a27052204034d1200184805220310120c072806270504031012002a0bb9
|28=>0x10122600075d0b1c05040310120c0bb32f050403101200072a481c040310120c0b0504031012bb0c07170b05040310120007440b050403101200070b050d04031012a10c0b14040310122b0007440b0f050403101200070b0f340d0310120c2a0b340d040310120c240b0f050d0310120cba0b05040310120007500b050d034d
|29=>0xb340403101200070b0529040310120c070b0504031012260c07170b050403121a00070b0504031012bf00072a270f0d0310120017180b1c05040310120c2a0504034d123f00070b050d04031012bd00280b050d034d1012000b1c050403123d00070b050403a01200071848050d0310120cbc0b05040310120007280b050d03
|30=>0x5040310123d00070b341c32040310120c280b04031012900007281824052203120007240b1c0532040310120c280b34040310120c072a2705220d0310120028180b050403123d00070b050403126e0c070b050403c0101200070b2f1c0403101200070b0504032d10122c00070b05040310124e0c070b0566040310120c0717
|31=>0x180b059e0310120007730b0f050d031012000b0f04031012c200070b040310123e780007500b0e05040310120c07270f040310122b00070b050403671012330c07c10b05040310120c0b050d0310123f0c0b1c0504031012560c0b690504031012330c070b0f04031012720007060b1c0504031012001d0b05040310120c070b
|32=>0x1012600c070b0504031012c60007280b050403131200071824052203120c070b0504031012520c07650b05040310120cc50b050403101200070b1c0504031012470c0b050d04031012be0c0b340504031012330c070b050d031012c40c0b05040310125c0c07240b0e05220403120c07230b05220403120c0b34040310128b0c
|33=>0x180b050d0310120c171805040310120100070b0f056a0d0310120c0b79050d0310120c2a050d0310123f00070b0f340d034d1200180b1c05220310120c110b050403123d0007240b0f050d034d12002a0b0d0310123e00070b1c040310122b0c0b0504031012c90c072a270f04034d101200c70b040310123e0007240b050403
|34=>0x7180b050d035810120c0b0504031012570c07240b0f1c040310120c110b0504030200070b349e040310120007180b0504031012410c07272f05040310120007420b050d0310120007240b140f05040310120c2a0b1c04035810120c0b1c040310123e0c11240522031200070b0504031012610c070b05040364101201000728
|35=>0xb05040310124f0c0b05ce040310120c07cc0b05040310120c17060b0504031012000b050d031012300c0b1434040310120c0b050d031012250c0b05a20403101200070b050d034310120007230b0e05040310120c0b050d04031012010c0bcb050403101200072a27056a0403101200240b1405040310120cca240522031200
|36=>0x240b3805040310120c07280b05040310129c00070b340d0310122e00072827050d031012000b0504031012d10c07d00b05040310120c440b1405040310120007230b0532040310120c27050d040310122b0006110b050403101200280b1c04031012260007182734050d031012002a0b140d040310120c18cf05040310120007
|37=>0x72427050d04031012000b0f05040310124500070b05040310122c00070bd3050403101200071824050d03101200075d0b05040310120c070b7f1c05040310120c0b1c05040310123f0c460b050d03101200070b05320403101247070b0504031012d20c07110b0f050d0310120c0b1405220d0310120c2a2705040310129600
|38=>0xb0504031012c300070b0f0e040310120c070bd5050403101200070b05040310127b00070b05040310125b0c070b340532040310120c07281827050403101200070b0504031012d400070b05040310128300070b05040310129900070b05040310128e00070b05040310124500072a0b056a040310120007a30b050403101200
|39=>0x310122b00070b6305040310120c070b0f05031012d700070b0504031012d600070b0f05040310122600070b0504031012010007890b050403101200070b0504034d10122e0007270b34050d0403101200240b0e05040310120c07180b34050d0310120007180b050403121a0007230b05040310120c0b0f0504031012010007
|40=>0x101296000718270504034d1012000b141c05040310120c0b0504031012d900072a0b140403101200070b0e0522040310120c070b0504031012d80007270504031012300007280b050d03101200072a0b7904031012000717110b050403101200070b05290403101200070b0504031012970c070b05040310122600070b050d04
|41=>0xb79050403101200070b05040310122b0c072a0b1c2204031012000728180b052203101200070b0f050d034d1012002a0b050d04034d1012000b9b1c05040310120007060b05040310120007280b340403101200070b1c05040310129300070b050d0403121a0007240b0532040310120c070bda05040310120c072a0b050403
|42=>0xe050d040310120c0b0522031012af00070b0f34040310120c07240b0f05040310120c070b0504031012470c070b1c040310122e0007500b0504034d1200072a0b0504035810120c07dd0b050403101200070b05040310123e0c070b0504031012dc00070b05045403101200070b050403db10120007730b0522040312000727
|43=>0x5220310120007280b0504034d101200070b0504031012de0007b10b05040310120c070b3404031012b50007184805040310120c07180b7f0504031012000718241c050403101200076c0b05040310120c070b0504038c10120007180b05220310120c0718240522031200072a0b05040310128600070b0f040310129000070b
|44=>0xb050403581012070b050403131200072a2705220403101200070b05b6040310120007a80b05040310120007cd0b05040310120c070b1c05040310124500070b05040310126f0c070b050403df10120007ca0b052203101200072a27340403101200070b05b90403101200078f0b050403101200072a270f040310120007110b
|45=>0x40310123f0c070b34050d040310120c0b1405040310124500070b8834040310120007180b341c040310120007240b8805040310120007180b050d0310120c0b050403e11012000724270504034d1200422a0b050403101200070b1c05040310120100070b05a7040310120c072a0b1c040310120c7a0b050d04031012000748
|46=>0x1012410c070b0504031012c40c070b0504031012e300070b0504031012b200070b0504031012e200070b140504031012010007240b05220d031200077a0b05040310120c07730b0f05040310120007270b14050d0403101200280b1c040310120007180b14050d0310120007270b340504034d1200500b050d03101200070b05
|47=>0x10120c07270b052204034d1200240b05910403120007180b0522034d12000717280b0504031012000728180b05040310120c070b7905040310120c070b0504031012e40c1823050403101200070b0f3404034d120007240b0f0504034d120007240b050d040310120c2a27050d040310120017180b050403101200070b050403
|48=>0x72a0b0532040310120c070b050d0310129700070b05e6040310120007b80b050403101200070b0504031012e500070b0504031012300c070b1c04031012b50007480b1c05040310120c0b0504031012250c0728110b05040310120007a50b05040310120c07170b050d0403101200070b0504034d1012af00180b05040358
|49=>0x1200070b050403121a0007180b1c05040310120c2a0b0504031012260007cf0b05040310120007282705040310120007110b0504034d101200590b050403101200070b3405040312300007270b0f050d03101200e70b050403101200070b05040310125600070b0504031012840c070b0f05320310120c071827340504031012
|50=>0x70b0f340d03101200077a0b0504034d1200072a0b340d040310120007240b0f050d0310120007730b050d04031012000b0504034d123f0007240b1c052204031200070b34050d04034d12000b050d0310123e0007500b1c050403101200070b0504031012e900070b0f040310122b00070b0504031012e80007240b056a0403
|51=>0x120c0b2f050403101200070b14050d040310120c42280b050403101200072a0b0f040310120c07240b050d04034d1200270504031012b50007ea0b05040310120007270b05220d031012000b0504031012530c07480b053204031012070b3405040358120c070b1c0504035810120c0b0504031012ab00070b0504031012770c
|52=>0x2a0b0522040310120c070b05040310129200070b050403ee10120007ed0b05040310120007ec0b050403101200072a0b04031012900007710b0f0403101200070b0504031012a10c07270b0f0504034d1012000b050403eb101200072a0b34040310120c070b790504034d12000717180b1c050403101200070b056a0d040310
|53=>0x504031012560007c80b050403101200070b0504031012f000070b0f0504031012b70007180b0e05040310120c070b05040310122e0c07110b05040313120007710b05220403101200070b0504031012bd00070b0522040358120c070b05ad040310120c070bef05040310120007180b05910310120007710b34040310120007
|54=>0xd04031012be0007502705040310120007270b056a0403101200180b056a03101200077a0b0f0403101200072a0b88040310120007230b052204031200070b34040310128b00070b0f7f040310120007110b050d040310120c281824050403101200070b0504031012b700070b05320403581012070b050d0310123f00070b1c
|55=>0x50d03101200070bf4050403101200070b0504034d12770007180b1c05220310120007480b3405040310120c070b1c040310122b0007f30b050403101200072427052204031200070bf205040310120007650b050403101200070b0f050d0310120c180b0504031012c300072a0b050d040310120c0bf1050403101200070b05
|56=>0x7480b0504031012470c070b05040310121a0007240b1405040310120007240b0f1c040310120007270b05040310129600180b05031012960007280b0504031012260007240b140f050403101200070bf5050403101200070b1c040310123e0007182405040310120c0728180b050d03101200070b0f056a0d03101200070b79
|57=>0x5040310120007ca24050403101200072a0b140d040310120007180b05040310129000070b05040310124f00072a0b3404034d120007180b050d034d101200170b05040310120007180b3405040310120c070b050d0310123000071124050403101200070b143404031012000706180b050403101200070b050d040310120100
|58=>0x1a00070b05040310127200070b0532040310123b0c070b05f6040310120007110b0f050d03101200070b1405220d03101200070b1c0532040310120c270504031012970007110b34050403101200072a0b052204034d120007480b0522040310120c070b053281040310120c280b05040310120c070b05220d0310120c28060b
|59=>0x70b0504031012b400070b0504031012f80007230b0f050403101200070b05040310127c00070b0f040310127800070b0504031012c200070b05040310128600072705040310122b00070b05040310128b0c0b053204031012330c076c180b05040310120c070b05f70403101200070b1c05040310123f0007110b05040312
|60=>0x1200070b05040310123b0c07c70b0f0403101200070b0522040310127800072a270504034d1012000b0504031012f9000724270f050403101200070b0504031012ae0007480b050d040310120c0b0504031012b50c071873050403101200070b0504031012600c070b34040310127800070b0581040310120c0b050d03101277
|61=>0x4034d1200070b0f1c040310120c0b95050403101200070b0504031012fb00072a05040310123f00070b059e0403101200070b140f05040310120c0b0504031012330c07c70b340403101200071827052203101200072a0b040310123e00077a0b1c0403101200070b0504031012fa00072a0b0f0d0310120007180b05040313
|62=>0x3101200070b050d0403131200070b9b050403101200070b05040343101200070b050403101293000728500b050403101200070b341c040310120c2a0b05220d03101200070b1c0504031012300007420b05040310120007240b1c05040310120cc70b0522040310120007420b0f050403101200070b1405040310120c182405
|63=>0x72a0b05910403101200070b050d04035810120c0b3805040310120c07710b1c05040310120c0b05220d034d1200170b1c05040310120007270b0f340403101200070b050d0310122e00070b1c0522040310120c850b0504031012000728180b1c0403101200070b14056a040310120007270b05040310123e00070b791c04
|64=>0x2a0b040310128b0007110b14050403101200070b0504031012be00070b14050d04034d1012007a2705040310120007550b050403101200072a0b0f04034d10120007240b05220403120c071728180b05040310120007460b05040310120007500b05040310120c071827050d031012002a4805040310120c070b34040310122e
|65=>0x4031012e400070b05040310129000070b3405040310120c07240b050d0403101200070b0f05040310120c070b34050d040310120007270b050d0403101200180b050d0310120007280b050403101200070b0532040310120c072a0b1c040310120007280b0f05040310120007180b34050403101200072a0b7f040310120007
|66=>0xd040310120007730b050403101200070b14050d0403101200070b340504034d1200070b050d040310120c240b05220403120007500b050403101200070b8805040310120007180b1c050403101200070b0522040310120c07180b0504034d10120007240b05040310120c072a27050403101200070b0504031012b500070b05
|67=>0x70b05040310123e00070b0f050d03101200072a0b050d040310120007282a0b050403101200070b05040310122b0007182705040310120007110b050d0403101200070b052204034d1200070b050403101297000711180b05040310120007240b0504034d120007500b052204031012000750240b050403101200070b056a
|68=>0x70b790f050403101200077a0b050403101200070b7f050403101200070b05910403101200070b05040310123f00070b05040310128b0007270b0504034d1012000b0f0504034d101200070b05220d0310120007710b050403101200072a0b05040310120c07180b052203101200070b0f34040310120007240b0f0504031012
|69=>0x4031012af00070b0504031012d700070b1c05220403101200070b05040310123000070b341c040310120007480b05040310120c07240b1c050403101200070b056a0403101200070b14050403101200070b0f1c0403101200077a240b0504031012000728180b050403101200070b79050403101200070b140f050403101200
|70=>0x3101200070b7f1c050403101200070b05040310127700070b0504035810120c07ca0b050403101200070b05040310127800070b0504031012e00007110b050403101200070b050d04034d1012000b056a220403101200070b790522040310120007180b05040310120c070b0504031012960007710b1c050403101200070b05
|71=>0x72a0b0504034d101200070b05040310122e0007270b3405040310120007712a0b05040310120007270b0f0504031012000750180b050403101200070b141c050403101200072a0b05220403101200072427050403101200072a0b340403101200070b1c05040310120c230b050403101200072a0b0f040310120007c70b0504
|72=>0x7270b050403101200072a0b050403101200070b1c050403101200070b0504034d101200070b0522040310120007240b050403101200070b34050403101200070b0f050403101200070b05040310120c070b050d0403101200070b0e05040310120c071824050403101200077a2a0b05040310120007270b05220403101200
|73=>0xb05040310120007180b0504031012
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xe7001dc0007
|7,0=>0x2ea00b3702ae00a38026e00938022e0083801ee0073801ae00638016e005380131c044800f20034800b2002480075c0158
|8,0=>0xb4e42ca90b0a02ba80ac642a980a86029890a45c28a70a064279809c242688098202588093e4246908fa0236808ba02268087a0215908360204907f201f4807b201e48076e41d29072641c1806e241b0806a201a080662018f9061a417e805d6416d80596015d80552414b9050a413a804ca01299048601189043e4106903f640f5803b240e48036e40d29032a00c28
|8,1=>0x4ec9138e44da9134644c89130204b7912be04a6912764495812360484911f20474811b2046481175c455811324443910ea4432810aa04228106644109101e43fe90fd643ed80f9603dc90f4e43ca90f0643b890ec5c3a890e7e439690e36438580df6037490db2036480d6e435290d2a034190ce2432f90c9e031f80c5e030f80c1a42fd90bd602ed80b9602dc9
|9,0=>0x1c8a471991c3e870691bf646f491bae46e291b6646cfa1b1a46bd91ad246ab91a8e069a91a4a068991a024677919be06678197a46568193a0645918f24633918a686209185e460e9181645fc917ce45ea9178285d6a173a05c5916f245b3916aa45a281666459181622457ea15d6456d81592455c81552054c8150a853a814c64528914820518814420507913f684f58
|9,1=>0x255e494e9251a093d924d2492c82492091b9244a49099240248f8823be48e5a237248d39232e08c2922e648afa229a489d92252488c8220e487b821ca48699218248579213a4845920f24832a20aa08219206608118202247ff91fde07ee91f9647dba1f4687c981efe87b691eb287a481e6e479291e26478091dde476f81d9a475e81d5a074d91d12473c81cd2072b9
|9,2=>0x2e5e0b8da2e160b7c92dca8b6992d824b5792d3a4b4592cf24b32a2ca64b2092c5e4b0e92c1a0afd92bce8aea92b828ad792b3a4ac682af64ab492ab20aa392a6a4a9282a2a0a80a29da8a6d9298e8a5a929428a48828fe4a36928b64a249286a8a12828264a00927de49ef8279a49dd9274e89ca9270649b9826c609a89267e4996926364984925ee4972925a649609
|9,3=>0x37064db8936be4da78367a4d95936324d83935ea4d72835a64d5fa355e0d4e9351a0d3d934d60d2c934920d1b9344e0d0a9340a0cfa833c64ce9833824cd79333a4cc5932f24cb4832ae4ca2932664c92732264c81831de8c6e931964c5c931520c4c8310e4c3a930c64c289307e4c169303a0c0592ff60bf582fb60be492f720bd392f2a4bc282eea0bb192ea24b9f9
|9,4=>0x40020ff793fba4fe593f724fd2a3f264fbfa3ede0faf83e9a4f9ca3e4e4f8a93e064f7893dbe4f6693d764f53a3d2a4f4193cde8f2f83c9a4f1d93c4e8f0a93c064ef893bbe4ee693b764ed493b320ec2a3ae64eb093a9e4e9e93a5a0e8e83a164e7ba39ca4e68a39820e579393a4e45938f24e33938a68e21838624e0f9381a4dfe837d64ded837924ddb9374a4dca8
|9,5=>0x48de522e94896521ba484a52099480251f8847be51e78477a51d68473a11c6846f651b4946ae51a29466651909461e517f845da516d94592515c8454e5149a45025137944b691249447211148442e5101a43e250eea439650dd8435250cc8430e50ba942c650a89428210979423a5085941ee9072941a650618416250508411e503e940d6502ba408e101a9404290088
|9,6=>0x4ada52ad94a92529b94a4a528994a025276a49b292639496e12529492a1240a
|10,0=>0x542a5501953de94ee9539294daa534654c7a52f694b4952ae54a1a5262548ea5216547ba51ca5469951825457951369444950ee5432950a6541fa505a540d9501253faa4fc653e894f7e53d5a4f3253c394ee693afa4e96939ba4e4a538a84e02937794dba536594d72535394d26933fa4cda532d94c92531b94c4a5308a4bfe52f694bb292e394b6a52d194b2252bf9
|10,1=>0x5d5e574da5d12573b95cc69727a5c7a5714a5c2e570295be656f095b9a96dd95b4e96c9a5b0616b895ac216a6a5a72969395a2e1681a59e256708599a965d95952564b959069638958be56269587656149582e5602957e655efa579a55dd9575255cb9570695b7a56ba55a59567255948562a9581955e2556f9559a555ca554e554a955065537a54ba55259547255139
|10,2=>0x668e599a966465988965fe5976965b65963a656699509651e593da64d2592b9648699189643e5906963f658f5863b258e2a636658d09631e58be962d658ac9628e589a962465888961fa9874a61ae58629616658509611e583e960d6582c9608a98199603e980695ff297f395faa57e195f5e97cda5f1257bc85ece57aa95e82979795e3a5784a5dee577295da657609
|10,3=>0x6fc25be796f769bd3a6f2a5bc196ee25baf96e9a5b9e86e529b8b96e0a5b78a6dbe5b6696d765b5496d2e5b4296ce65b3096c9e5b1da6c525b0b96c0a5af8a6bbe5ae696b729ad2a6b265ac096ada9aad96a925a9b96a4a5a8996a025a76a69b65a649696e5a52969265a40968de5a2da68925a1b9684a5a07b67fa59f5967b259e2a676659d09671e59be966d659ac9
|10,4=>0x79169e3c978ce5e2a978865e189783e5e07877fa5df5977b25de2a77665dd09771e5dbe976d65dad8768e9d99a76425d86a75f65d74975aa9d619755e9d4da75125d3b974c69d27a74769d149742e5d03873e69cf09739a9cdca734e5cca973065cb8972ba9ca5972725c93972269c7fa71d69c6c9718a9c58a713e5c46970f29c31b70a25c1f9705a5c0ca700a9bf99
|10,5=>0x82026077981b6a0649816aa05198122603ea80d6602ab8086601898042200797ffa5ff4a7fae5fe297f665fd187f1e9fbda7ed25fab97e8a5f98a7e3a9f84a7dee5f7297da65f6097d5e5f4da7d161f3ba7cc69f2897c7e5f15a7c2e9f0387bea5ef287ba65ee097b5e5ece97b165ebc97ace5eaa97a865e9897a3e5e86979f65e74979ae5e61a79625e4f9
|11,0=>0x8b5262cb98b06a2b898abe62a698a72a292a8a26627fa89d6a26c9898e625a989466248988fe6235a88b262239886a62119882261fea87d661ec9878aa1d8a873e61c6986f2a1b3986aa61a0a865e618da860ea179a85c26166a85766155885326143984ea6130a849e611da8452610b9840a60f9983c260e798376a0d49832aa0c1982e260af9829a609d9824ea089a
|11,1=>0x241c9904e6409a8ffea3f5a8fb263e2a8f62a3cea8f12a3baa8ec2a3a798e7a639688e36638498dee6371a8da2635f98d5a634d98d12633b98cca6328a8c7aa31598c326302a8be662f098b9aa2dd9
|12,0=>0x247e991d6646c9918e645a991466448990fe6436990ba24259
|13,0=>0x24878
|_,_=>0
def wAt:=mkWire dB 252 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb0d4101d2407c001d041042c410b04414310504444430b0d4001d170bc4415131244440180742c11050c444400007414110b0d41431000744c49111002c35040740c09050244c4911100601d0b0441426030244c4911100601d0b0440c09131244440180742c111312444401707c4415180742c11050d4001d1312444400b0d4101d13124143111100001d050442c35
|1=>0x74101d0f10c14110b054001d040745c431707c4415180742c111713c441511100601d0b0442ced103982ce20f0c414110531440ce0b3281031040746015051042c1d0b044141d103382cca040c4001d0507414c11810c001d0b044001d2e0742c3e050441431111002c3500074101d0b074101d042b4a8430b054101d0b074a043180542c1105044001d131244440
|2=>0xb0442cf900074101d0f10c141113124601511100601d0b0442c3e00074101d050441441050c444430b0d4001d04074001d0b4545043050d4101d170bc181d2807c60150b044001d0507460150b044001d102e4101d0b0f81411050244c4911100601d0b044001d281046015040742c11111005c2f11054601d0b0446105040742c410b0441431000742c8a0b0541041
|3=>0xb044001d050742c150b22810412407c103105044001d0b104603a0b044101d050c4001d1110c5c2f11054601d0b044001d0407410ad2a10c2c1504074001d2810c60150b044401d040742c150b22810412e07414410b0f8001d050442c350e04c101d050c4001d0b4b814ed3210c10312a3201031000742c1505074141d040c41411000742c414810c101d0b0c4001d
|4=>0x40742c1d2a0d0101d0b05414110b044901f000742c410b3e4001d0f10c141d050445c4f110544440180742c1110538101d4804c2c3100074001d1710c2c51050d4101d3107440ce0b32810310007410410b104101d050c4001d0407460410b04414310007414112a10c101d0b0542c1d0507440b90b0f8001d05044001d3e0743c430b054141104074601505104001d
|5=>0x1710c607105074001d0b044141d0007410ad2a10c2c151710c7159181cc141d0b044001d05074a043180542c111707c5c2f180742c113810c3c3100074141123044901f050c4001d0b10444400007414110b0d4101d0407461620b0444031000742c11050c42c1d05304101d1810c2c1105564001d181cc141d0b0445c43170bc4415180742c11000744c49111002c35
|6=>0x4074a843050442c1500074101d630743c330007414110504444430b0d4001d04074141d053382cca040c4001d0507414ca040c4001d0b1057c0f240e41431000742c410b104141104074143100074a04318054101d0b0742c11050742cca040c4001d050757417240c4001d0b1042c3a05044101d050c4001d050444c49111002c350407410410b104141d000742c11
|7=>0x40c440cd0b3281031000742c1d040743c430b05414110530460430b044001d0407444401707c4415180742c11044e4603a0b04414310007410410b1042c11050c4001d05328103100075401f24044001d0b104901f0007410410b1042c1104104901f000742c41170bc5c432807460150b044001d100142c520407414310b228104100074101d11100001d0b0d41435
|8=>0x407414310007414351110c2c3500074101d110544c4911100601d0b044101d0b0742cf90f10c1411030244c4911100601d0b044101d180e02c11050c4001d0e044143100074344105044101d050c4001d000742c520b04414350407414351312444400b0d4101d0b074a04118054101d0b04414311810c2c1100074101d040c4a843000742c1505075a443053342cca
|9=>0x103342cca040c4001d05588141d100c4001d05074001d0f0cc1411000742d050e10c14310007444431707c4415180742c1105044901f050c4001d0b1045c43181c4141d000742c1104074001d2810c60150b044101d6c10c6031000742c110b3b4141d3210c103100074101d6c0bc6031000742c112a10c14350b054001d0407414310007414110b0d4101d0e10c1411
|10=>0x180544443180742c11041042c11050c4001d6c10c2cc9040c4001d0407520130b0c4001d0f1042c720507414111007460410b0742c1105228104100074101d1c328141d040c4001d2a10c2c15040c4001d6c1002cc9040c4001d0610ca01f180542c112407c1411000742c410b074a8340b054101d041049c410b0742c1104074401d0b228104104725c443270542c1d
|11=>0x1810c141d000742c112a044401d0b0542c1d0447520430b0c4001d0407410ad2a10c2c1504074a043180542c110b6a82c150d104101d050c41411000742c410b074a043180542c1110074101d3404414412b07414112a10c2c15050442c3a050c4001d103342cca040c4001d2e07414410b0f814112a104001d0b054141d053342cca040c4001d050442c1500074101d
|12=>0x40742c3e000741411053b4c843040c4001d100c4104100074101d180541441040742c1105074001d180542c11000743441050d4101d0b1049c11100742c1d05224001d04104141d050742c150b228104105814c81f040c4001d111002c3500074101d1c1042c3e050741411100182c52050d4101d0b14870110507414410f0cc1411000742c410b054104100074101d
|13=>0x50741031000741411040c4001d0b054141d050d4104110074101d240e41431000742c41050c4001d0b2281041102c4b81d0b0f814110583490360b104101d05104a01f180542c112a10c2c150007414111710ca01d180542c11102e42c3e0507414110b3b4c843040c4001d0b074a8410b054101d0b044101d050c4001d3e0743c430b0541411181c4141d000742c11
|14=>0x1710c4415180742c11000742c35050d4101d170bca01d180542c110407410410b0742c412907410ad2a10c2c150b0e8101d050c4001d8910c2e210f07c14111710c2c51050d4101d0b04414350b074101d0407460410b0742c110b864a88a041042c15131244440180742c1105044c81f040c4001d1710ca01d180542c113207c2c15040c4001d4805c141d0b0c4001d
|15=>0xb074401d050442c410b0743c430b0541411055646073050742c11100142c520f07414112e0742c3e000741411058e46137100742c110b044101d000742c411312444400b0d4101d053046043000742c110b3b4c843040c4001d10074101d0522810410504441e10b1c8141d0b3e43c430507414110b104101d050c4001d3210c2c15040c4001d1c04c001d0b054141d
|16=>0x2a10c2c1500074101d06104a01f180542c11100c4001d05074144193074708a04104141d2810460150b0742c111810c2c11050c4001d2a10c2c150f07c14111707c2c51050d4101d180547041050742c110b0441041100742c1d000741441040742c110b0442c412207c10411110014110b0d4101d2807c101d180542c110b9047043050741411100142c52050d4101d
|17=>0x5074a043180542c110407520430b0c4001d00074708a04104141d2722810410b0542c1d1110c2c3500074101d0b1482c35050d4101d277983c41050442c1d1805c101d0b0742c11050d42c1500074101d103382cca040c4001d04074401d041042c15059642c150d10c101d0b0c4104100074101d2a0442c1500074101d2807c6015040742c111707c4415180742c11
|18=>0x102c8b81d0b0f81411050742c3e0007414110e10c14310007414119e10c11e10b1c8141d1710c6071050742c110b0742cf90f10c141126074a043180542c110b0742c410d104101d0b0442c410d104101d040746031000742c110b054001d04104141d00074708904104141d0507410ad2a10c2c150547520430b0c4001d180e02c11050c4001d3210c2c31040c4001d
|19=>0x40742c110b104401d04074344104074143100074001d2810c60150b0442c4105074001d0b04411e10b1c8141d6c10c6031000742c11180e82c11050c4001d100742c1d0b34414410b054101d0b07414410b5881031100c4001d0407414110b0742c416c0bc6031000742c1128074a043180542c1127104101d0b0742c1117100a01d180542c110b0442c4104104141d
|20=>0x5104a8410b054001d04074a8c80b054103100075e81f000742cd1051044443050442c3504074103105044001d0b1042c1d042b4a8430b0545c432807460150b0442c1d040743c43050445043000747011050769c1f045844031000742c1d2810c60150b0442c151410c143504076940f0b0e41431000742c3100074141d051042cca040c44031000768c430b6a43441
|21=>0x4074141d2807c60150b04414691110c601d0b0442c8904104001d040742c3504074143100074e01f0f0c4001d0504450430f074001d0504440050b148143504075b013180c4001d0b044001d0b044141d0510444400b0d41435040743843040741431000746015051042c1d0b044a843040742c15050445c432807460150b0442c52000747011050741411040742c1d
|22=>0x504414c10407460430b044001d0f10c2c1505044c81f3210c103100075581d181cc141d0b046b41d220cc10410007414691110c601d0b044a834040742c15050443441040742c1d0b0445c43270f414110b0741441270f814110b07410410b044901f0b104401d040742c15050442c520f074001d050442c4104104001d04074a811000742c1505074001d0b0441435
|23=>0xb044fc1d0b0542c8a041041411040741431000746015040742c1d0b044a81d0f10c2c1505044141d0b3281031000744c4911100601d0b0445c2f2807460150b046c41d180cc001d0b0442c410b0441431000742cca3207c103100074001d0b0542c8a04104141d3210c1031000741041100742c3604074001d0b044901f0b104441511100601d0b0442ce20f0c4001d
|24=>0x40746043040742c1d0b0442c1d2807c60150b044101d1805c001d0b0442c52050d42c1d040749c1104104401d0b0742c520b0441435040748c1500074901f0b10412dd240fc14110b104a813000742c15050742c110d10c2c1d040745c2f2807460150b04414ca05074103100074101d100742c3e0504440b90b0f8001d05044a8350b054001d0407416d1300746043
|25=>0x50742c114810c2c31000749c410407410410b074101d0f10414110b074001d0b3e43c43050442c3e1c10c141d050458c1d0f0cc001d0504414410b0f8001d050442c1504104401d0b07410410b0c4001d0b044a01f180542c1d0b0442c15049047043050748c1100074901f0b1042c15050d42c1d040745c2f11054601d0b0441441100742c150b074143104104001d
|26=>0xb044141d0b0c4001d0b054e0430f0c4001d050447159181cc141d0b0442d151410c143504074101d0b588403100074a8431c0442c15050742d151410c3c1d05044001d0407414110510414410b054001d04074101d05044001d0b1042d3d3e0743c4305044101d18104401d0b044001d0b104104105074001d040743c430504444430b0d4143504074001d0b2241041
|27=>0x5104001d042b4a8430b054001d2810c60150b04444151110c601d0b0442e56059643443040742c1d040742c1505044607105074001d0b0442c15100742c8a04106f81d2a0dc2c1504074a8110b054401d040745c43181c4141d0b0445c40270f414110b074101d0b0c4001d0b044aa590b054344304074101d2810c60150b044141d240c4001d0b104bc1d053046043
|28=>0x50742c110b4143843050c4001d1710c9c3d050442c1d050741441040c4001d180547043050742c111805410410b1042c11040c4141d000742c41180541441000742c110b054101d041042c1d1710ca01d180542c116c10c2cc9040c4001d10ab49c3e050442c1d05304141d1810c2c112e0742c3e05044603a0b044143100074116d0b0e814310007460710b044141d
|29=>0x240c4001d0b1041041050c4001d0b104001d04104901f0b104001d05104701305074130d181c8141d0b044101d2710414110b0742dfe1c104141d050442c720f10c141d0504460410b04414310007414110b074a8430b0542cca040c4001da507c2c39050c4001d0b228104100074101d000746073050742c11053342cca040c4001d05045c443270542c1d1707c6071
|30=>0x40743c430b05414112a10c001d0b054141da510c2c39050c4001d05044401d0b0542c1d2a07c3c430b0541411053281031000742c41c810f1c112a07c2c15180544440180742c110007410410b1042c111053920130b0c4001d5007c9011000742c41189047043050742c110507520430b0c4001d2a0dc2c1500074101d0b3281031000741162040744031000757417
|31=>0xb044a04118054101d0b0443c1d05044001d0b1044031000742c1505074001d0f10c141d050449c11041042c1d0b10414ce0b3281031000742c52050d4101d04074001d180542c11170bca01d180542c110007414110d104101d05224104100074101d040742c150b228104110074101d0504414410b044001d04104141d1710c4415180742c1104074401d050442c41
|32=>0x50443813040741431000767841047842c720507440b9040742c3e05044901f050c4001d0b1042c52050d4001d04074bc1f0530460430b0441135100742c150b074001d0f07414110b10410411807c2c410b044101d0b04440310007461620b044403100074141d05044001d0b1044c4911100601d0b0441441047842c720507438430b04414310007414c11810c2c1d
|33=>0xb044c0311810c001d0b045b01f0b3241031000742d151410c143504074103100074901f0b104a843040742c150b074601d2807c60150b044141d2810c60150b0442c11040742c1d0510414350b054001d040742f0d181c8141d0b044001d3e0743c430504411050e10c143100077341d2a0cc001d0b054181d2807c60150b04460430b044001d0407414410f074001d
|34=>0x40742c1d0b10450430f07414112e0742c3e0504414fd0b2281041040742c410b0449031000742c41000747041050742c8a000741041050742cf9040743c430504520430b0c4103100074ac3100074a8430b054001d050442c3504074143504104001d040742c150d10c2c1d040743c3105044001d0b104981d2810c60150b0442c3e040741411051046015040742c1d
|35=>0x5044401d0b0f81411040742c1d051041431000742c4105104101d0b0444443180742c1100074901f0b1042c520f0741411181c8141d0b04414310007414117907cd01105104ac1d2a10c2c150b0e81431000741441040c4001d180542c1d0b0454017181042c11240d82c41040749c8a041042c1d184dc401d0b0445043050d4101d0b0543441040742da90d104101d
|36=>0x100c4001d0b054344304074401d0b0742c110007470110507415aa0d104101d1c0442c15050741041050c4001d7a04c2cd10510460430b0742c1118054101d0b0442c1534044144111054601d0b04410ad2a10c2c151805c001d0b044a043180542c1104074a8430b0543c330007414112404c14110b1042de63404414412810c2c3d050442c52050d4101d0b8843c1f
|37=>0xb0f8141d050446041100742c110b0544031000742e452207c10410f10c001d050444417180742c112a0d02c1504074425d1805c2c112710410410b0743c41050442c1d00074a8430b05410410b054141d0410460150b044141110074101d0b054401d04074708904104141d2807c60150b044a8110b05414411c22810410507444430b0d4101d040c4001d0b1041561
|38=>0x50742e411c10c141d0b0742c15050449c11041042c1d18054401d0b0449072050742c41180cc001d0b04414412a04c2c150b0c4001d0b0447041050742c11050742c410b0442cc9040c4001d107842c72050741041000742c11041042c410b044a88a041042c151c10c141d05044101d050c4001d041042c3604074144100074141105044001d0b10520430b0c4001d
|39=>0x507414410b1043c1f050442c1100074101d10b54a8130b054401d0b0742c412a22410410b0542c521c044141d04584403100074001d0b054141d2a1042c15040742c31100c4001d11100601d0b04410410b0542c1d04e0490170b105e81f0b34414412a0cc001d0b05450431c044141d05588403100074422d1c04c141d1807c10410b04414410b0542c1d049047043
|40=>0x4074001d0b104101d0b0542c1d2807460150b0443843050c4001d04588403100074a937100742c153f0742c8a04104708b04104141d0b148143504074101d041042c41000742cd1051049c41050442c1d050d42c1d04074a8110b054141d0b0441435040741441100742c1d18104101d0b044001d0b228104105104001d040745043050d4101d051043c1f050442c11
|41=>0x50748c152407c2c412a22c10410b0546043000742c112a04c2c1505074141d0b0c4001d0e04c143100074601d180542c110b0e41431000742c51050d4101d100742c36040742c11100c4001d04104401d0b0742c412207c104104104401d0b044a01d180542c110007460150b044001d340441441050d8001d040742c112407c2c4110074141105104401d050442c41
|42=>0x4104141d0f4dc401d0504414112a10c2c151834c2c11051042c410d104101d1110c601d0b044141d000742c112810ca8110b0542e2d1c04c141d180542c1d0b0449c11100742c1d23044901f0b10414411810c2c110407414110b0771c412a07c2c15181cc141d0b04520170b0c4001d040c4001d0504414410b0742c110b0541031000746017040742c111c2201041
|43=>0x2810460150b0442c150007414110b104401d04074a8130b0542c1d0b964344304074101d041042c1d4804c2c31000742c31040c4001d05104403100074141d100c4001d270f814110b074001d05228104104074141105104401d0b3441441040742c1505104101d050442c41271042c1d04074401d0b22810410b104104105074144110074101d040743c43050442c89
|44=>0xb0541041100c4001d220cc10410007416bd0b0d8101d0b044881f041042c710507414410007410410b055dc1d05228104110af42c36040742f91050d8101d7a0742cd10510470430b054141d0b1c4141d050442d62100c4001d05044401d0b0744391050d8101d0b054001d05104401d340441441181c4141d0b044344100074101d0530460430b044143500074101d
|45=>0xb0742c110b0743441040742c110d104101d050442cd1051042c150f07c141104104901f0b10414411c04c141d1c104141d050442c3500074101d0b10460150b044903f050442c41040c4403100074101d0b2281041181cc141d0b0471c112a07c2c152a0d82c1504074903f050442c410b0441431000742c3e00074141111100601d0b0442c7104104141db5074a813
|46=>0xb1043c1d0504416452207c10410f10c141d050442c11000742c410407460150b04414110d104101d04074d01105104175d2404c2c4110074148a041042c1104104141d0b0c4001d05104a8430b054141dca104601f0b04410410b0742c41240f014110b105401f181042c1104074001d050446072050742c110b054001d0407620410f07c14112a0dc2c15040746041
|47=>0x4074a01f180542c111807c2c410b0442c15050d4101d1c10c141d0b044f81d0f10c1411100742c1505104101d100742c11270f414110b0741441000742c110407460430b0449c110b0742c411c044141d05104a01f180542c110b14814350407520430b0c4001d1110c601d0b0443c1d050442c410b104141d0504434430b074101d0b044344304074a043180542c11
|48=>0x3407414412a22810410b0542c1d2a10c2c15000747013050742cca040c4001d180c4001d0b044a888041042c150b2281041050744443180742c117110c9c150b074c843040c4001d181c0141d0b04414110b0d4101d04104143504074141d040c4001d1805c2c1d0b0449c110b07414411007410410b0542c3104104001d3207c1031000742c3d00074141104104001d
|49=>0x40742c15050444440180742c113210c10310007414112a07c2c150b1c8104105074401d0b0542c1d7104c9c150b07414110b0742c419707460170b0442c3100074101d00074a8130b0549c410b0742c11053281031000742c720507414413207c103100074101d0522810413007460430b044d03604074144105044901f0b1042daa0d104101d0b1c8141d050442dfe
|50=>0xb044001d0507414410407410410b054141d1810c2c117a0442cd105104141d000742c4104104a81f0b054903d050442c410f074001d050442c41100742c1105074001d0504416590d10c101d240f814110b1042c150b2281041047842c72050743c1d0007414110b32810310007414412a07c2c15041042c1d0b0443c430b0541411050742cd105105fc13340741441
|51=>0xb0742c110b0c4001d0b05414410b0f814110b054881f04104101d100c4001d0f0c4001d05044001d0b1c4141d04104401d040746071050742c11050442c1d05104101d0b0f81411000741041050742ddd0522810410507460150b0443441050d4101d0f10c14110b074141d340441441111002c350407415a90d104101d102e42c3e05044708a04104141d181046015
|52=>0xb054143604074704305074001d051042c4104074001d05044101d051042c1d04074101d0b04460150b0441031000742c15050742c3d050442c110510470410b054141d1c04c2c15050742c35050d4101d2a0dc2c1504074401d050d4101d0b0742cd10510728151807c2c11100742c15050441041000742c412807460150b0442cf90f10c141124044001d0b104101d
|53=>0x40749c150b074001d0b05410410b04414110510414110b1043c43050441411040742c1504074a8110b054a8430b0542c1d0b0442c350407410411007460170b044601d0b044401d0b1042c890410490110b104344104074901d0b104143504074401d05104001d0407410410b10460410b0443c1f05044141d0b044104100074401d0b044001d0b1042c150b074a813
|54=>0xb0442c720507490170b104601d0b044401d04074881d04104148904104001d0b0443443040742c71050742c360407490130b10410410507460430b044141d051042c3100074141d0b104344104074143504074141d0504490150b10460150b044d011051043c1d050443c41050442cd105104d01d05104881f041042c8a04104701305074401d0b074401d050441041
|55=>0xb0442c1d0b054141d1007410410b104144105044001d040741431000742c410b044a8410b05410410b074401d0b0542c3e050442c1d05104a81d0b05414110b07460410b04470110507410410b0542c1d0b1042c1505104001d05074901f0b1042c1505044a81f0b054704105074148a04104403100074601f
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x600000000
|7,0=>0x3e60395034500000000000002e600000295000002360000000001d60176012500c60000000000660000
|8,0=>0x164415f515a51555153214e51495144513f513a51364131512c51275122511d51185113510e5109510450ff50fa50f550f050eb50e650e150dc50d750d2500000ce40c950c450bf50ba50b550b050ab50a650a1509d40985093508e508950881083507e50795074506f506e106a406640000061505c50575053404e504950445
|8,1=>0x2762273326f426a52655260525b525652515000024c52475242523d52385233522e5229522452213000021c52175212520d52085000020351ff41fb41f651f151ec51e751e251df31db41d651d241cd51c941c451bf51ba51b641b151ac500001a751a2519d51985194418f518a51855180517b500001765171516c51684
|9,0=>0x3744370436c436843644360435c435843544350434c434843444340433c433843344330432c432843244320431c431843144310430c43084304430042fc42f842f442f042ec42e842e442e042dc42d842d442d042cc42c842c442c042bc42b842b442b042ac42a842a442a0429c429842944290428c428842844280427c42784
|9,1=>0x4744470446c446844644460445c445844544450444c444844444440443c443844344430442c442844244420441c441844144410440c44084404440043fc43f843f443f043ec43e843e443e043dc43d843d443d043cc43c843c443c043bc43b843b443b043ac43a843a443a0439c439843944390438c438843844380437c43784
|9,2=>0x573456f456b45674563455f455b45574553454f454b45474543453f453b45374533452f452b45274523451f451b45174513450f450b4507450344ff44fb44f744f344ef44ec34e844e444e044dc44d844d444d044cc44c844c444c044bc44b844b444b044ac44a844a444a0449c449844944490448c448844844480447c44784
|9,3=>0x673466f466b46674663465f465b46574653464f464b46474643463f463b46374633462f462b46274623461f461b46174613460f460b4607460345ff45fb45f745f345ef45eb45e745e345df45db45d745d345cf45cb45c745c345bf45bb45b745b345af45ab45a745a3459f459b45974593458f458b45874583457f457b45774
|9,4=>0x771476d476947654761475d475947563752474e474a47464742473e473a47364732472e472a47264722471e471a47164712470e470b3707470346ff46fb46f746f346ef46eb46e746e346df46db46d746d346cf46cb46c746c346bf46bb46b746b346af46ab46a746a3469f469b46974693468f468b46874683467f467b46774
|9,5=>0x86f486b48674863485f485b48574853484f484b48474843483f483b48374833482f482b48274823481f481b48174813480f480b4807480347ff47fb47f747f347ef47eb47e747e437e047dc47d847d447d047cc47c847c447c047bc47b847b447b047ac47a847a447a0479c479847944790478c478847853781477d477947754
|9,6=>0x8a748a3489f489b48974893488f488b48874883487f487b487748734
|10,0=>0x96839653962395f395c3959395639533950394d394a394739443941393e393b393839353932392f392c3929392639233920391d391a391739143911390e390b39083905390238ff38fc38f938f638f338f038ed38ea38e738e438e138de38db38d838d538d238cf38cc38c938c638c338c038bd38ba38b738b438b138ae38ab3
|10,1=>0xa283a253a223a1f3a1c3a193a163a133a103a0d3a0a3a073a043a0139fe39fb39f839f539f239ef39ec39e939e639e339e039dd39da39d739d439d139ce39cb39c839c539c239bf39bc39b939b639b339b039ad39aa39a739a439a1399e399b399839953992398f398c3989398639833980397d397a397739743971396e396b3
|10,2=>0xae83ae53ae23adf3adc3ad93ad63ad33ad03acd3aca3ac73ac43ac13abe3abb3ab83ab53ab23aaf3aac3aa93aa63aa33aa03a9d3a9a3a973a943a913a8e3a8b3a883a853a823a7f3a7c3a793a763a733a703a6d3a6a3a673a643a613a5e3a5b3a583a553a523a4f3a4c3a493a463a433a403a3d3a3a3a373a343a313a2e3a2b3
|10,3=>0xba83ba53ba23b9f3b9c3b993b963b933b903b8d3b8a3b873b843b813b7e3b7b3b783b753b723b6f3b6c3b693b663b633b603b5d3b5a3b573b543b513b4e3b4b3b483b453b423b3f3b3c3b393b363b333b303b2d3b2a3b273b243b213b1e3b1b3b183b153b123b0f3b0c3b093b063b033b003afd3afa3af73af43af13aee3aeb3
|10,4=>0xc683c653c623c5f3c5c3c593c563c533c503c4d3c4a3c473c443c413c3e3c3b3c383c353c323c2f3c2c3c293c263c233c203c1d3c1a3c173c143c113c0e3c0b3c083c053c023bff3bfc3bf93bf63bf33bf03bed3bea3be73be43be13bde3bdb3bd83bd53bd23bcf3bcc3bc93bc63bc33bc03bbd3bba3bb73bb43bb13bae3bab3
|10,5=>0xd223d1f3d1c3d193d163d133d103d0d3d0a3d073d043d013cfe3cfb3cf83cf53cf23cef3cec3ce93ce63ce33ce03cdd3cda3cd73cd43cd13cce3ccb3cc83cc53cc23cbf3cbc3cb93cb63cb33cb03cad3caa3ca73ca43ca13c9e3c9b3c983c953c923c8f3c8c3c893c863c833c803c7d3c7a3c773c743c713c6e3c6b3
|11,0=>0xda32da12d9f2d9d2d9b2d992d972d952d932d912d8f2d8d2d8b2d892d872d852d832d812d7f2d7d2d7b2d792d772d752d732d712d6f2d6d2d6b2d692d672d652d632d612d5f2d5d2d5b2d592d572d552d532d512d4f2d4d2d4b2d492d472d452d432d412d3f2d3d2d3b2d392d372d352d332d312d2f2d2d2d2b2d292d272d252
|11,1=>0xde92de72de52de32de12ddf2ddd2ddb2dd92dd72dd52dd32dd12dcf2dcd2dcb2dc92dc72dc52dc32dc12dbf2dbd2dbb2db92db72db52db32db12daf2dad2dab2da92da72da52
|12,0=>0xdf51df41df31df21df11df01def1dee1ded1dec1deb1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 16
def pmP:Nat→Nat
|0=>0x8026ec000000000007026870000000000040210d0000000000040168f0000000000040140600000000000103cad000000000001034ad000000000001007ad00000000000100408000000000000e04a9000000000000126ef000000000000126ed000000000000124ad000000000000124ac0000000000000c00c0000000000000840c0000000000000800c00000000000002caf000000000000026ce000000000000020210000000000000200c000000000000020000000000000000180100000000000001001000000000000007ec00000000000000400000000000000000880000000000000001800000000000000008000000000000000060000000000000000500000000000000000
|1=>0x40a048b000000000040634ad000000000040624ad000000000040436ad000000000040424ad000000000040234ad000000000040224ad000000000040084080000000000400800c00000000004003cad000000000040036ad00000000004003021000000000040026af000000000040026ad0000000000400268f0000000000400268b000000000040025af000000000040025ad00000000004002587000000000040024af000000000040024ad00000000004000904000000000040007ad00000000004000000000000000030000000000000000200000000000000001c036ad00000000001a0168d00000000001003cad0000000000100300800000000000d036ad000000000008127ec
|2=>0x48025ad000000000048024ad000000000047034af000000000047024af000000000047016af000000000046024af000000000045436ad000000000045424ad000000000045036ad000000000045035ad00000000004502dad000000000045024ad0000000000444048b00000000004440089000000000044036af000000000044036ad000000000044034af000000000044034ad000000000044024ad000000000043004af000000000042a16af000000000042804af000000000042234af000000000041426ad000000000041026ad000000000041024af000000000041024ad0000000000410008d00000000004100000000000000040e16ad000000000040a36ad000000000040a24ad
|3=>0x7001004000000000060064af00000000005a406af000000000058e37ad000000000058e36ad000000000058c37ad000000000058a37ad000000000058837af000000000058437ad000000000058426ad000000000058024ad000000000055035ad00000000005404008000000000054024af000000000054024ad000000000052086af000000000050e36af000000000050e17ad000000000050026ad000000000050025ad000000000050000a500000000004b024af00000000004a4068b00000000004a4048700000000004a024af000000000049424ad000000000049024ad00000000004900489000000000048425ad000000000048424ad000000000048027ad000000000048026ad
|4=>0xd4406af0000000000d4406ad0000000000d4036af0000000000d4036ad0000000000ca016af0000000000c9426ad0000000000c9004870000000000c8426ad0000000000c8420ad0000000000c8036ad0000000000c8024ad0000000000c8000a10000000000c5436ad0000000000c5424ad0000000000c5036ad0000000000c5034ad0000000000c5026ad0000000000c5016ad0000000000c403ead0000000000c4036ad0000000000c4034ad0000000000c0424ad0000000000c0225ad0000000000c0036ad0000000000c0026ad0000000000c0024ad000000000094030ad0000000000900378d00000000008d026ad0000000000810268f0000000000810168d00000000008004400
|5=>0x800018090000000008000000800000000080000001000000000648024af000000000448024af0000000004480048b000000000440004ad000000000408004080000000003500c00c0000000002840940c000000000260066af000000000260064af0000000002540c0080000000002440a68f00000000024302683000000000243024af000000000242036af0000000002200648b0000000002100b008000000000207034a7000000000205004a70000000002000000000000000015802000000000000148024ad00000000014000000000000000100000080000000000dc036ad0000000000d8037ad0000000000d502ead0000000000d5026ad0000000000d4426ad0000000000d4424ad
|6=>0xc4d00489000000000a40004af0000000009500a006000000000950000060000000008c8036ad0000000008c8024ad0000000008c1424ad0000000008c040289000000000858037ad000000000850026ad00000000084a026af00000000084a024af000000000848424ad000000000848027ad000000000848026ad000000000848024ad000000000845024ad0000000008440200000000000084400000000000000843024af000000000841436ad000000000841024ad00000000084100408000000000840a34ad0000000008404068b000000000840034ad000000000840024ad0000000008400248b000000000840020890000000008400080800000000084000400000000000810034ad
|7=>0x4158024ad000000004154436af000000004154436ad000000004154034af000000004150026af000000004150026ad000000004148024ad000000004144424ad000000004144034ad000000004140024af000000004140024ad0000000040c5026ad0000000040c5022ad000000004050004af000000004040024ad000000004040004af0000000040100002a000000004010000000000000020c5624ad0000000020c4636ad000000002045624ad000000002040636ad000000002040626ad000000002040624ad000000001440024af000000001400024870000000011400000a0000000010500048900000000105000000000000001040024af0000000010010000000000000100000000
|8=>0x8040234ad0000000061d0626ad0000000061d0226ad0000000061c5624ad0000000061c0624ad0000000061c0424ad000000006155426ad000000006140424ad0000000060c4436ad0000000060c4236ad0000000060c0224ad000000006045424ad000000006044624ad000000006044234ad000000006040224ad000000006040204af0000000049d0026ad0000000049d0024ad0000000049c9424ad000000004958026ad0000000049580268f000000004958024af000000004858024ad000000004850004af000000004448024af0000000041d5426ad0000000041d4036ad0000000041d0426ad0000000041d0026ad0000000041c8426ad0000000041c5424ad0000000041c0024ad
|9=>0x100c1026ad0000000100c0424ad0000000100c0224ad0000000100c0034ad0000000100850348d000000010052026af000000010051036ad00000001005102ead00000001004f0368f00000001004f0358f00000001004f034af00000001004c024ad000000010048226ad000000010048024ad000000010043024af0000000100414268d000000010041024ad00000001004100004000000010040424ad00000001004040487000000010040034ad000000010040024af000000010040024ad0000000100400028100000001000c0000c00000000e144224ad00000000e0c4220ad00000000e044224a900000000e044204ab00000000c044024ad00000000c044004af0000000080c4224ad
|10=>0x1804d034ad000000018049025ad0000000140c8024ad000000014048024ad000000014040025ad000000010cd0037af000000010c5003eaf000000010c4d024ad0000000108d8037ad0000000108cc036ad0000000108cc024ad0000000108c0036ad0000000108c002dad0000000108c0024ad000000010898037ad000000010852036af00000001085003ead000000010850036ad00000001084d424ad00000001084d024ad00000001084c036ad00000001084c020a9000000010842036af000000010841026ad000000010840036ad000000010840024af000000010840024ad0000000108400058d000000010442024af000000010440206890000000100d14268d0000000100cd034ad
|11=>0x460c4634ad0000000460c0626ad000000046054636ad000000046045626ad000000046044634ad000000046040626ad000000044148024ad000000044144034ad000000042140034ad000000042041024ad000000042040024ad0000000408c0424ad000000040851024ad000000040840834ad000000040840426ad000000040440024af0000000400c5e26ad0000000400c0e26ad000000040051025ad000000040050e36af000000040050e36ad000000040050826ad000000040045e26ad000000040044024ad000000040041826ad000000040041024af000000040041024ad000000040040e26ad000000040040024ad00000001c04d234ad00000001c04d034ad00000001804d234ad
|12=>0x90042024af000000090040224ad00000009004002cad000000090040024ad000000084140025af000000084140025ad0000000814410000800000008084002cad000000080056025af000000080054025ad000000080046035af000000080044035ad000000080042005af00000008004002dad000000080040025ad000000060252026af00000006004102483000000050841e36ad0000000500c0424ad000000050041026ad000000050041024ad00000004c0d4236ad00000004c0d4234ad00000004c054236ad00000004c045234ad00000004c044224ad000000048045034ad000000048045024ad000000048040034ad0000000461c0424ad000000046150426ad000000046140424ad
|13=>0x1000000024ad00000100000001c8d000001000000000890000008040400c4af000000804000000060000008000406c00c00000080004020006000000800000080080000004d0041024ad000000442050024ad00000040000100008000000210840224ad000000210040225ad000000210040024ad000000200200280080000002000c0a26ad0000002000c0a06af000000200040225af000000200040225ad000000200040224af000000200040224ad000000200040201ad000000200040025ad000000200000200080000002000000000400000011000c124ac000000100004124ad000000091440024af0000000910000058f000000090841026ad000000090840424ad0000000900c0024ad
|14=>0x10000c8224ad0000010000c8025ad0000010000c000404000001000060220af000001000058026ad000001000050024af00000100004a405af00000100004a025af00000100004a007af000001000048425ad000001000048424ad000001000048225ad000001000048027ad000001000048025ad000001000044035ad000001000044025ad000001000041034ad000001000040425ad0000010000404200000000100004040587000001000040024af000001000040024ad000001000040021ad000001000040020080000010000400000000000100002c0468b000001000028064af0000010000010848f000001000001025ad0000010000004040c000001000000025ad000001000000024af
|15=>0x101004c024ad000001010048224ad000001010048027ad000001010048025ad000001010048025a5000001010048024ad00000101004042dad00000101004040daf000001010040025af000001010040025ad000001010004024ad000001004158027ad000001004158025ad0000010041580258f000001004150007af000001001442025af000001001440025af000001000a40024af0000010008c8226ad00000100084c426ad00000100084c024ad000001000848426ad0000010008480a6af0000010008480a4af000001000848024af000001000840024ad000001000448027af000001000444035af0000010001580230c0000010001480230c000001000148004ad0000010000ca005af
|16=>0x1080444035af000001080050027ad000001080048027ad000001080044035ad000001044148024ad000001042040024ad000001021042025af0000010148c00368d000001014048024ad00000101404002dad000001014040024ad000001011440025af000001010cc8036af000001010c4c036af000001010c4c024af000001010c48024af000001010c48007af0000010108c8036ad0000010108c8024ad0000010108c44248d0000010108c0424ad00000101084c024ad000001010849424ad000001010848024ad000001010844024ad000001010840004ad00000101044c025af000001010440224ad0000010100c8025ad0000010100c8004a500000101004c03cad00000101004c025ad
|17=>0x20010410000000000200100100000000002000848436ad000002000848024ad0000020000d5026ad0000020000d5024ad0000020000c90068b0000020000c5036ad0000020000570268f000002000057024af000002000055026ad000002000054024ad000002000052026af000002000050026ad000002000049024ad000002000048024ad000002000045024ad000002000041424ad000002000040025ad000002000040024af000002000040024ad000002000009027ad00000200000103cad0000018000602008b00000144c848024ad0000010904c002daf0000010900c002dad00000109004602d8f00000109004402dad000001090042007af00000109004002fad000001080448027af
|18=>0x30108c0024ad00000301084c024ad000003010040024ad0000030010500258f000003000c58024af0000030008c9224ad0000030008c9024ad0000030008c8026ad000003000858026ad000003000840024ad000003000458007af0000030000570258f000003000048425ad000003000048027ad000003000048025ad000003000048025a5000003000048024ad000003000040025ad000003000040024ad0000022000d1026ad0000022000c0024ad000002200040025ad0000020908c0424ad000002090041024ad000002080050025ad000002056140024ad0000020560c0424ad000002056040424ad000002040051426ad000002010840024ad00000201004c425a500000201000d024ad
|19=>0x400800000008000004006144234af000004006140224af000004006140034af000004006054236af000004006046235af000004006044235ad000004006044234af000004001040004af00000400005a004af000004000058024ad000004000054024ad000004000050024af000004000040236ad000004000040224af000003800c58026af000003414840024ad000003290c40024af000003202048225ad000003094c50036af000003094851036ad000003094440025af0000030908c0024ad000003090851024ad0000030900c0025ad000003090040425ad000003080055025ad000003056848024ad000003040849426ad000003040849424ad000003016050025ad000003010c51024af
|20=>0x10001040024af0000100002600e4af0000100002600a4af0000100002440a4af0000100002400a6af000010000200000040000100000640e6af000010000060064af000010000044206a3000008000200020a9000006056c50024af0000060568d0024ad000006056050024ad000005002040024ad000005000440235af000005000040235ad000004c040500848f0000048002402e68f000004404050024ad000004402850004af000004402840024ad000004200040024af000004080042225af000004080040225ad00000404c0400048f000004048050024ad000004040041024ad00000401004002cad00000400e044224ad00000400c040024ad00000400a040004af000004008040224ad
|21=>0x80000040024ad000044200040224ad000044002840024ad000043000848224ad0000420000c9026ad00004141884d024ad000041200040a25af000041200040a25ad000040040848024ad000040040049024ad000040000049024af000040000041024ad00004000004100000000020000084136ad00002000000003cad0000148000602a4af0000140002402e4af000014000060024af000012a02240024af000012041050024af000011010a40024af000011001048025af000010203040224af000010040051024af000010011c40024af0000100041600e4af000010001c48024af000010001c40024af000010001440025af000010001044024af000010001044024a7000010001040224a7
|22=>0x802000c4236ad000080200046234af000080200044234af000080200040235ad000080090040224ad000080060043024af000080040051024ad000080040041824ad000080040040024ad0000800120c0636ad000080010040224ad0000800028c0624ad000080002840636ad000080002840634ad0000800020c0634ad000080002040e26ad000080000841024ad00008000084002cad000080000442024af0000800000c8024ad0000800000c4634ad0000800000c0e06ad000080000049024ad000080000048426ad000080000044624ad000080000044234ad000080000043024af000080000041026ad000080000040a24ad000080000040624ad000080000040226ad00008000004002dad
|23=>0xc0200040224ad000090220042064af000090200043024af000090000046224a7000087202048225af000086a02058226af000086202c48224af000086202858226ad000086202048224ad000086002048224ad0000842000c0236ad0000842000c0234ad0000840000c0024ad000084000040024ad000083012848224ad0000830108c1424ad000083010841424ad000082042041425ad000082002048626ad000082002048624ad0000820000c1424ad0000812100c023dad000081210042225af000081210040225ad000081010840224ad000080410840024ad0000802108c0224ad000080210842234af000080210040234ad0000802008c0236ad0000802008422368f000080200840236ad
|24=>0x80000085a037af0008000002470368f000800000207034a7000487043051025af000486243051024af000484202252226af000484202242224af000410291c42024af000410220057024af000410200247034af000410060242024af000410021c42024af000410021242024af000410005040024a7000410001642065af000410001040024af000410000252026af000410000247036af0004040061d0226af000404000040236af000403000040025af0004020000520258f000401291442025af000401080058027af0004000000d5026af00020000004200caf000200000040004af000104046050024af000104005050024af000100003050024af0000c1018840224ad0000c0202040024ad
|25=>0x6010001040004af005000000c48004af005000000440004af002010004150024af00200000004120404001012001450024af001000011441000040010000011500200a001000001150020080010000011500000e00100000095002000001000000840004af000c90200242236af000c10001240024af000892201042024af000890200242234af000890200053226af000890000246234af000812201442024af000811011642025af000810011e42024af000810005040024af000810001c42024af000810001642025af000810001242024af000810001240024af000810001040024af000810000246036af000810000246034af000810000242036af000810000242024af000802201442025af
|26=>0x200040000500200002000101084c024ad02000101004d024ad020001010008024ad020001000045420000200000108040248d0200000100cd036ad0200000100cd034ad02000001004d036ad02000001004d035ad02000001004d034ad02000001004d024ad02000001000c0390c0200000100040240d02000000084502000020000000840024ad0200000008400200002000000080c024ad020000000054025ad02000000004503dad020000000044424ad020000000044024ad020000000040024ad0200000000000180501200000004400404010010011440025af010010001050024af010010001040024af010010000040024af00d000000840024af007000000040004af006010001050004af
|27=>0x200003080440425af200003080055435ad200003080040425ad2000000c0050025ad200000042041024ad200000000041024ad20000000004100000100010000a40024af080008000240024af0600000000040390c040801080448027af040801000448007af040401000058007ad040001080040027ad040001000858027ad040001000848027ad040001000048026ad04000000085a027af040000000858027ad040000000840026ad040000000840024ad040000000840004000400000000dc037ad0400000000d8037ad0400000000d4017ad04000000005c037ad04000000005a037af04000000004a004af040000000048024ad040000000040025ad0400000000040390c020004000050024ad
|28=>0x800000001040004af800000000256024af800000000247034af400000011442024af200080200040025ad200080002041024ad
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x200000
|7,0=>0xd00c02000000000900002000110000004805010090000001c00
|8,0=>0xe13b9a7025bb700cd078172a8ab5101b8a018ac49704c1c3b8006e424080c31cc004b80a00c9414c09004373b9b848c03004be6a029508a7208e6000e3a58dc33a3e391c607e7c02c004b00c730be01a7f0c58f09c52710bd0560200c68020b10386b298224a0992e4df6a8ef2b8090c0c70584420000029a3396971a5a61900f305bd71e39048c4024aa2983f2e8bd0d0e00280a0994a6d42d0a0114c0d8
|9,0=>0xa4439c1c85bc88e83c46b4d48cce12d38bf4e8c5c71c9328b34c8c0904ed8dd2518021224456095d70dc2d904d3f8141696610863188b76662430b67d491da1699315382918a819a5cf9ffcf5f0aaa141eb786c6b40ca568105525747860b25721f26d70c694c4d86e45efb6cf420ce501164d2a6e165e0cb158c5c6d737751bb53d714468c26a2ee1390038a7caf9457f12f3dce4e2329084f11cb2abfcee19
|9,1=>0x7b46a17f058c6d4cbb5a56e87544bfbc28e2793b16c843b025a3de1888f37d5ef26ab556760b55e9501fbd18130644c0df3f6b2ac3a5210d9cbd2d07d01c1129637e96f0ae30491eadd30d81765d71639ecb6cd3733271d95061ac14c4cc2add6589b1a4a3083ce18d72098c22775d215ddf20c4975465ba334fcde45ca6a4597ea143cac735064d112115e077045076cc58d7e5f31eba6b94b6cd13f2a73b2f
|9,2=>0x3c9412075b8ed5a06a769cf066f89f954b5deabb6f31fd26d67c513c3ada7cab28b47fd2cca78b097651639c434df481befa10263b78a36045e7e1ee82d32cdcc54d27e2c281b67315423f6430204110c2819409d517cad4a443379af790b877dbfa29ca9715e57f36562e249ce217b4daccb41f9ca4c4cc8a4c583b610f4237b1d00af24b3f51c0f5fcb1da73d63c5dfc776709810bbcd7d9f47d8aa7abf11e
|9,3=>0x6bac8a8382274784ff35d3c6555b84e176a
|10,0=>0x6a770476954376880366bad886b233dc63c994ff145b746b01dcaa97de6bcc82bb94f5a2d4387b14df2c79a56db020db7d4d1b05d92323df8f7a8b81b7512b9dd4a6ec196d0abf5de5ef18a00673192b6151b9692aba1608f4cbae35097a9028b3cab5a224a205c9fdabdb62814bbc48d62c5d595392f0f9c01ebdacd019a4ca9a3523cf0dbd917a2bda1298ceb5860c326ad685cd8e5dd0376f63bfcfdc137f
|10,1=>0x3d43eb1b2d7e584454a8a18d515949add4e6256e5a6648351191e53275613d7106c1d15143586e9c19c8cba99dc64493592099ee4321671b61a85a03bf8d95aa6ebb3765b34adbaba84181682c4bd721c971bc445e126579126843104b091190c769e4657f8715e845656076495524e828d0dbb984eca6a58eaa715c3aa35b21ca21ca29ed66ab53c48c5ad1454eb80535be47048a62600fb5534cabb154bec3
|10,2=>0x99a23da59c1de9433e099f753b26782332b8c5b4c3de7898ea8725925a8947f561f0959b4325dab60e962c2ee065a9266ee389dd7451d8db07567b627974390acb85e61dee0e136a8822dc92598438cfc899f406a492b411067411d09b61d2e003a4f993d13830e9ad246ced144e29479a8c908e2d2cc33f8470cd78f855c749d6ef165e68d8a141652d54d7c99657d1f321cf4d75e3af9d63f3571eef8
|11,0=>0x29d5e26fbd1a117a4b894da61e1db6d009742f3c5fa4a77d0eb131502e3d48c0f2d0bd84f0ca251b4f5a204d93b2766964349d291b54bddd3af293bb8390e591228d39c95351ac693d79178d151e0a4a48b270e815091462834996b46b6d8b83344586179949c4583d9526706d0ba2c3e8d48c88814134a7df682a2f
|12,0=>0x4d219290b83b0e4f58ac5e0b032
|13,0=>0x2b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 68 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_63 9 roots_63 ops++addP pm 2 dom_247 11 roots_247 ops++addP pm 3 dom_239 11 roots_239 ops++addP pm 4 dom_235 10 roots_235 ops++addP pm 5 dom_191 12 roots_191 ops++addP pm 6 dom_116 5 roots_116 ops++addP pm 7 dom_251 12 roots_251 ops++addP pm 8 dom_111 8 roots_111 ops++addP pm 9 dom_119 8 roots_119 ops++addP pm 10 dom_223 11 roots_223 ops++addP pm 11 dom_79 6 roots_79 ops++addP pm 12 dom_85 5 roots_85 ops++addP pm 13 dom_127 11 roots_127 ops++addP pm 14 dom_45 5 roots_45 ops++addP pm 15 dom_175 9 roots_175 ops++addP pm 16 dom_252 9 roots_252 ops++addP pm 17 dom_245 8 roots_245 ops++addP pm 18 dom_125 9 roots_125 ops++addP pm 19 dom_117 6 roots_117 ops++addP pm 20 dzo_213_2 6 roots_213 ops++addP pm 21 dzo_167_64 6 roots_167 ops++addP pm 22 dom_215 8 roots_215 ops++addP pm 23 dom_231 8 roots_231 ops++addP pm 24 dzo_117_2 6 roots_117 ops++addP pm 25 dom_47 6 roots_47 ops++addP pm 26 dom_253 11 roots_253 ops++addP pm 27 dom_95 9 roots_95 ops++addP pm 28 dom_93 7 roots_93 ops++addP pm 29 dzo_183_64 7 roots_183 ops++addP pm 30 dzo_47_16 6 roots_47 ops++addP pm 31 dzo_111_16 7 roots_111 ops++addP pm 32 dzo_175_64 7 roots_175 ops++addP pm 33 dzo_253_2 8 roots_253 ops++addP pm 34 dom_221 8 roots_221 ops++addP pm 35 dom_213 6 roots_213 ops++addP pm 36 dom_207 8 roots_207 ops++addP pm 37 dom_61 6 roots_61 ops++addP pm 38 dzo_245_2 7 roots_245 ops++addP pm 39 dom_77 5 roots_77 ops++addP pm 40 dom_212 5 roots_212 ops++addP pm 41 dzo_93_2 6 roots_93 ops++addP pm 42 dom_205 6 roots_205 ops++addP pm 43 dom_173 8 roots_173 ops++addP pm 44 dzo_239_16 8 roots_239 ops++addP pm 45 dom_237 9 roots_237 ops++addP pm 46 dzo_125_2 7 roots_125 ops++addP pm 47 dzo_187_64 7 roots_187 ops++addP pm 48 dzo_191_64 8 roots_191 ops++addP pm 49 dom_84 4 roots_84 ops++addP pm 50 dom_229 6 roots_229 ops++addP pm 51 dzo_221_2 7 roots_221 ops++addP pm 52 dom_157 7 roots_157 ops++addP pm 53 dzo_175_16 7 roots_175 ops++addP pm 54 dom_189 10 roots_189 ops++addP pm 55 dom_159 9 roots_159 ops++addP pm 56 dom_165 5 roots_165 ops++addP pm 57 dom_149 5 roots_149 ops++addP pm 58 dom_183 8 roots_183 ops++addP pm 59 dom_167 6 roots_167 ops++addP pm 60 dom_55 5 roots_55 ops++addP pm 61 dom_199 5 roots_199 ops++addP pm 62 dom_103 5 roots_103 ops++addP pm 63 dzo_235_16 7 roots_235 ops++addP pm 64 dom_141 5 roots_141 ops++addP pm 65 dom_109 6 roots_109 ops++addP pm 66 dom_143 6 roots_143 ops++addP pm 67 dom_151 6 roots_151 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_213_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_167_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_117_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_183_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_175_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_253_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_245_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_239_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_125_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_187_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_191_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_221_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_zo_175_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h61;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h62;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h63;exact cpcs (by decide +kernel) lowS_zo_235_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h64;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h65;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h66;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h67;exact cpcs (by decide +kernel) lowS_151 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 22 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 22 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 127 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 127 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 398 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 14 384 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 398 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 z9_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 382 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 126 256 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 382 → Z 10 i = true := (range_split z10_0 (range_split z10_128 z10_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 99 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 99 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 11 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 11 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 1] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [2, 0] }, { op := GateOp.or, inputs := [5, 9] }, { op := GateOp.or, inputs := [10, 9] }, { op := GateOp.or, inputs := [3, 10] }, { op := GateOp.or, inputs := [3, 7] }, { op := GateOp.or, inputs := [1, 0] }, { op := GateOp.and, inputs := [4, 12] }, { op := GateOp.and, inputs := [15, 14] }, { op := GateOp.and, inputs := [11, 13] }, { op := GateOp.and, inputs := [8, 5] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51884_aux

theorem PEqualNP.Outside.L_meta_51884 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51884_aux.main
