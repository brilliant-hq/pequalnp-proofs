import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52668_aux
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

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefefe0000fefeeeeefefe0000fefeeeeefefe0000fefeeeeefefe0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccccc00ffccffcccccccc00ffccffcccccccc00ffccffcccccccc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeeeee00ffeeffeeeeeeee00ffeeffeeeeeeee00ffeeffeeeeeeee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcfccc00fffcffccfcfccc00fffcffccfcfccc00fffcffccfcfccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefeee00fffeffeefefeee00fffeffeefefeee00fffeffeefefeee00
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

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfff0fff0fff0fff0cc00cc00cc00cc00fff0fff0fff0fff0cc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffafffafffafffaee00ee00ee00ee00fffafffafffafffaee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xeeeeaaaaeeeeaaaaeeee0000eeee0000eeeeaaaaeeeeaaaaeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfcfcf0f0fcfcf0f0fcfc0000fcfc0000fcfcf0f0fcfcf0f0fcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefefafafefefafafefe0000fefe0000fefefafafefefafafefe0000fefe0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffaaffaaffaaffaaaaaaaa00aaaaaa00ffaaffaaffaaffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffccff00ffccff00cccccc00cccccc00ffccff00ffccff00cccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffaaffeeffaaeeeeee00eeeeee00ffeeffaaffeeffaaeeeeee00eeeeee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfff0fff0fff0fff0f0f00000f0f00000fff0fff0fff0fff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffafffafffafffafafaaa00fafaaa00fffafffafffafffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcfff0fffcfff0fcfccc00fcfccc00fffcfff0fffcfff0fcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffefffafffefffafefeee00fefeee00fffefffafffefffafefeee00fefeee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffaaaaaaaaeeeeeeee00000000ffffffffaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffff0f0f0f0cccccccc00000000fffffffff0f0f0f0cccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffafafafaeeeeeeee00000000fffffffffafafafaeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffff00ff00ffccffcccc00cc00ffffffffff00ff00ffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffaaffaaffeeffeeee00ee00ffffffffffaaffaaffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0ff00ff0000000000fffffffffff0fff0ff00ff0000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffaffaaffaaaa00aa00fffffffffffafffaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffff0fff0ffccffcccc00cc00fffffffffff0fff0ffccffcccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffafffaffeeffeeee00ee00fffffffffffafffaffeeffeeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffcccc0000cccccccccccc0000ffffffffcccc0000cccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeaaaaeeeeeeeeeeee0000ffffffffeeeeaaaaeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffff0f0f0f0f0f00000f0f00000fffffffff0f0f0f0f0f00000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafafafafafaaaaafafa0000fffffffffafafafafafaaaaafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcf0f0fcfcccccfcfc0000fffffffffcfcf0f0fcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefefafafefeeeeefefe0000fffffffffefefafafefeeeeefefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffaaffaaffaaffaaaaaaaa00ffffffffffaaffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffccff00ffccffcccccccc00ffffffffffccff00ffccffcccccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffeeffaaffeeffeeeeeeee00ffffffffffeeffaaffeeffeeeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffff0fff0fff0ff00f0f00000fffffffffff0fff0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffafffafffaffaafafaaa00fffffffffffafffafffaffaafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcfff0fffcffccfcfccc00fffffffffffcfff0fffcffccfcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffefffafffeffeefefeee00fffffffffffefffafffeffeefefeee00
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

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccccccc00cccccc00cccccc00cccccc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffafffafffafffafffafffafffafffafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcfccc00fcfccc00fcfccc00fcfccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffefffefffefffefffefffefffefffefefeee00fefeee00fefeee00fefeee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffccffcccc00cc00ffccffcccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f00000f0f00000f0f00000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffafafafafffffffffafafafafafaaaaafafa0000fafaaaaafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefefefefffffffffefefefefefeeeeefefe0000fefeeeeefefe0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccccccc00ffccffcccccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeeeeeee00ffeeffeeeeeeee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffafffafffffffffffafffafffaffaafafaaa00fffaffaafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcffccfcfccc00fffcffccfcfccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffefffefffffffffffefffefffeffeefefeee00fffeffeefefeee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccff00ff00ff00ff00cc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffaaffaaffaaffaaee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfff0fff0fff0fff0cc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffcccccccccccccccccccc0000cccc0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0fcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffefefefefefefefefefefafafefefafafefe0000fefe0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffccffccffccffccffccff00ffccff00cccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfff0fffcfff0fcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffefffefffefffefffefffafffefffafefeee00fefeee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffff00000000cccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffff0f0f0f0cccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffff00ff00ffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffaaffaaffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffff0fff0ffccffcccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffafffaffeeffeeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccc0000cccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffafafafafffffffffafafafafafaaaaafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffcfcf0f0fcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffefefefefffffffffefefafafefeeeeefefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccff00ffccffcccccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffaaffeeffeeeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffafffaffaafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffcfff0fffcffccfcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffefffafffeffeefefeee00
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
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
def isoMvS_196:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_41
def isoMvS_200:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_41
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
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xa0a00000a0a,8,9)] (by decide +kernel) lowS_42
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_slice_b [(0x303000003030000,1,17)] (by decide +kernel) lowS_41
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
|0=>0x204c1324d1404c12448d204c1
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
def isoMvS_53:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_29
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_29
def isoMvS_58:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 5:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_57
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_57
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_57
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 4:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_29
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_29
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_29
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_57
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_29
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_29
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_57
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_29
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_57
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_29
def isoMvS_116:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_29
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_57
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_57
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 4:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_29
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_105
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_105
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 4:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_29
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_57
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_57
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_105
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_43
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 4:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_29
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_57
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_105
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_43
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xaaaaaaaa,8,9)] (by decide +kernel) lowS_30
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xa0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_58
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_61
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(5,13),(5,21),(5,37),(8,9),(8,40),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,33),(32,40),(36,37),(36,44),(36,52),(48,49),(48,52),(48,56)]
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
|4,0=>0xb6d8e19fc8
|5,0=>0xa5e019bec497d24
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccc00cc00022002200220022cc88cc88cc88cc8b30033003300330000cc00cc0088008b333333300000000cccc0000cccc0003300330022002200c0c0c0c0c0c0c0c2222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x436109436104361084376104310543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 62 0x3fffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x182
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x19
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_53 4 roots_53 ops++addP pm 2 dzo_57_4 5 roots_57 ops++addP pm 3 dom_41 4 roots_41 ops++addP pm 4 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xcccc000000000000cccc,8,10)] (by decide +kernel) lowS_77
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_slice_b [(0xc0c0c0c000000000c0c0c0c,8,10)] (by decide +kernel) lowS_89
namespace S_94
def pG:List (Nat×Nat):=[(2,10),(2,18),(4,20),(4,68),(6,14),(6,22),(6,70),(8,10),(8,72),(12,14),(12,28),(12,76),(16,18),(16,20),(24,26),(24,28),(24,88),(64,68),(64,72),(66,70),(66,74),(66,82),(80,82),(80,84),(80,88)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_94.map (·&&&dom_94)
def gM:=goal_94&&&dom_94
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x46ac128199
|5,0=>0x4c25d3bd750c8a5
|6,0=>0x4c25d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x555555550000000055550000aaaa888800000000aaaa888955540000000000015554000002a802a8000000000220022550055000000000055005500a8a8000000000000a8a8000141414140000000014141414222222220000000022222222555555550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x64210642108642107642106215043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 95 0x7fffffffffffffffffffffff
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
|5,0=>9
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 4 roots_92 ops++addP pm 1 dom_78 4 roots_78 ops++addP pm 2 dom_30 4 roots_30 ops++addP pm 3 dom_90 4 roots_90 ops++addP pm 4 dom_86 4 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_94 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_92 4 s (0,roots_92.map (·&&&dom_92)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_94 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_92 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_94==dom_94)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_94 gM v ys):RunD true dom_94 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_94 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_94 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_94 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_94 roots_94 goal_94 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_94
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=S_94.noCircuit
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,8,10)] (by decide +kernel) lowS_105
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_slice_b [(0x3030000030300000303000003030,64,68)] (by decide +kernel) lowS_105
def dzo_106_4:=0x5050000050500000505000005050
def gzo_106_4:=0x5050000050500000504000004000
def gsh_106_4:=0x505000005050000050400000400
theorem lowS_zo_106_4_42:Lower true dzo_106_4 roots_106 gzo_106_4 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_4) [(dom_106,4)] (by decide +kernel) (lower_slice_b (T:=gsh_106_4) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_110
def pG:List (Nat×Nat):=[(2,10),(2,34),(4,68),(6,14),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,44),(12,76),(32,34),(32,40),(32,96),(36,38),(36,44),(36,100),(64,68),(64,72),(64,96),(66,70),(66,74),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_110.map (·&&&dom_110)
def gM:=goal_110&&&dom_110
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x32f7
|5,0=>0x38f3e
|6,0=>0xd04d3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x155540001540000015554000154022220000222200002222000022225555000000000000555500000000aa000000aa000000aa000000aa0141400001414000014140000141408888000088000000888800008805555000055550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8d51a3544688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 111 0x7fffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8d
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
addP pm 0 dom_108 5 roots_108 ops++addP pm 1 dzo_106_4 5 roots_106 ops++addP pm 2 dom_106 5 roots_106 ops++addP pm 3 dom_102 4 roots_102 ops++addP pm 4 dom_42 4 roots_42 ops++addP pm 5 dom_78 4 roots_78 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_110 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_106_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_78 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_108 5 s (0,roots_108.map (·&&&dom_108)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_110 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_108 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_110==dom_110)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_110 gM v ys):RunD true dom_110 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_110 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_110 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_110 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_110 roots_110 goal_110 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_110
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=S_110.noCircuit
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xa0a00000a0a000000000000000000000a0a00000a0a,8,9)] (by decide +kernel) lowS_170
namespace S_206
def pG:List (Nat×Nat):=[(2,10),(2,130),(4,68),(4,132),(6,14),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,76),(12,140),(64,68),(64,72),(64,192),(66,70),(66,74),(66,194),(128,130),(128,132),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_206.map (·&&&dom_206)
def gM:=goal_206&&&dom_206
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x29edf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5500000000000000550000000000000055000000000000005500a0a0000000000000a0a0000000000000a0a0000000000000a0a11110000000000001111000000000000111100000000000011112aaa80000000000000000000000000002aaa80000000000000005555000000000000555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 207 0x7fffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_204 5 roots_204 ops++addP pm 1 dom_142 5 roots_142 ops++addP pm 2 dom_202 5 roots_202 ops++addP pm 3 dom_198 5 roots_198 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_206 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_198 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_204 5 s (0,roots_204.map (·&&&dom_204)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_206 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_204 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_206==dom_206)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_206 gM v ys):RunD true dom_206 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_206 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_206 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_206 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_206 roots_206 goal_206 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_206
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=S_206.noCircuit
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
def isoMvS_55:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_62:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 7:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_61
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 5:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_31
def isoMvS_93:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_91
def isoMvS_103:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_79
def isoMvS_115:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_91
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_91
def isoMvS_118:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_94
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_109
def isoMvS_122:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_110
def isoMvS_124:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_91
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_91
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_109
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_109
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_91
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_109
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_61
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_107
def isoMvS_213:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_59
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_91
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_110
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_110
def isoMvS_227:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_230:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_206
def isoMvS_234:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_171
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_107
def isoMvS_242:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_110
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_110
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xaaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_62
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,18),(3,11),(3,19),(3,67),(4,20),(4,68),(5,13),(5,21),(5,69),(6,14),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,88),(64,65),(64,68),(64,72),(66,67),(66,70),(66,74),(66,82),(80,81),(80,82),(80,84),(80,88)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf8d839d66979aad724680baa9
|5,0=>0xf60b6f0415e715edbd85d96cfd44388fd2a7ba1269cdf664e459919563774db1d2b17629e5729d75
|6,0=>0xe6104e1f4be0f48d74e2d176bc9547c0c24c0be3a68449f05f77fc4757da6f9fe6f7b16b9df69cdf62b885b42757fd74fe624d1953ee1033bfe2794620c9f1fa651d70c1af8b1aa3c1617614c7f125580c1490682b042a303c1f
|7,0=>0xcb033bf2a1bc5fd92e45657cc4d195326322a996048d9
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff000000000000000000ff00ff0000000000ff00ff00333300000000000033333300ff00ff0000000000ff000000ffffffff00000000000000000000ffff000000000000ff00ffccffcc00000000cccccccc00ff00ff00000000ffffff00aaaaaaaa00000000aaaaaaaaffffff0000000000ffffff00ffffffff00000000ffff0000ffffffff00000000ffffff00ffff000000000000ffff0000f0f0f0f000000000f0f0f0f0cccccccc00000000ccccccccffaaffaa00000000aaaaaaaa
|0,1=>0xffffffff000000000000ff00ffffffff000000000f000f003333333300000000000000000000ff00000000000000ff00f0f0fff000000000f0f0fff00000000000000000330033003333330000000000333333000f0f0f0f000000000f0f0f00555555550000000055555500ccccccff00000000ccccccccfff0fff000000000f0f0f0f0ffffff0000000000ffff0000ffffffff00000000ff00ff0000ff00ff00000000ff00ff000000000000000000ff00ff0000ff00ff0000000000ff0000
|0,2=>0xf000f00000000000f000f00f0fff0ff0000000000000000ffff333300000000ffff0000ffffffff00000000ccccccccff00000000000000ff00ff00cccccccc00000000ffccffccffffff000000000000000000fff0fff000000000fff0fff0ffffffff00000000f0f0f0f000ff000000000000ffff000000ff00ff0000000000000000333333330000000033003300ffffffff00000000ffccffccffff000000000000ffffff000000000000000000ffccffccff0fff0f00000000ff00ff00
|0,3=>0xffccffcc00000000ffccffcc33003300000000003300330000000000000000000000ff0000f000f000000000f0f0f0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x1da2c33821d92c34c20400d34820471030811cf0ce04760b0ce0815cb0c204728f0ce0961cb14339504750e0811cb0d20811c34420474050ce0891c61420473c50ce0810033821cd2c63020472c308100a1850891c80c20471850810040c2040
|1=>0x1cb1033820472e63820472c344204794338204728b0d33820472c338204790b0e33820472e20ce0811cb0e13820472c380e0811cb0ce0811df2c50ce4420471833821d92c338204778b0d338204774339b0472c33822472c50ce0811cf0ce081
|2=>0x1cb0ce0ac0472c50ce0811cb0ce0811f22c3382047c4b5033820472c33820402c33b00472c34c20473c614e0811cb0ce0811cbb8338204740bb4e0811cb0d3382b011c33ab0811cb0ea3820472c33820472e90c204770b943a0e9c11cb50e081
|3=>0xce0811cb0ce0811dc2c33820472e50ce0811cb3c3382047bcb0f33820472c34ce081
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18ccc6062d315189cc4862130f546ec31615b09583ec196
|6,0=>0xb13d6deaad4f6a4b509e76f34797349de40f197893c2de08efe67bbbc59d6ce476ebb59d9eec8760bae9d66eac752ba79d2ee91645b211cfae776
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 52 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xce8e2e38b023a04e4e2d04b432d04e853a08fcb3838b0e2dbcb853b0dd412e38b433d38b034d38b433f38b0e2f38b8b3a70b4b3a181c33909c433a04f4e2c38b06070ce533f38b0e2d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x3000000000000000
|6,0=>0x80400001e2708006c5a1609710000000000001524c9123c80000000000e100000344c128800000821885100032
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf99f95bd1b5573d71d5003d93d531d2041100c10c008004002001401101000e00d005004002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000000040000000
|6,0=>0x580c1236070d00000141720a01800c001277800129c01
|7,0=>0x12adaf98ea79
|8,0=>0x18
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_94 7 roots_94 ops++addP pm 1 dom_86 4 roots_86 ops++addP pm 2 dom_87 5 roots_87 ops++addP pm 3 dom_31 5 roots_31 ops++addP pm 4 dom_79 6 roots_79 ops++addP pm 5 dom_83 4 roots_83 ops++addP pm 6 dom_75 5 roots_75 ops++addP pm 7 dom_77 5 roots_77 ops++addP pm 8 dom_93 6 roots_93 ops++addP pm 9 dom_91 6 roots_91 ops++addP pm 10 dom_29 4 roots_29 ops++addP pm 11 dom_89 5 roots_89 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_89 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_94 7 s (0,roots_94.map (·&&&dom_94)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_94 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_95==dom_95)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,8,10)] (by decide +kernel) lowS_109
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_121
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x30303030303030303030303030303030,16,20)] (by decide +kernel) lowS_121
def dzo_104_16:=0x1010000010100000101000001010000
def gzo_104_16:=0x1010000010000000100000000000000
def gsh_104_16:=0x101000001000000010000000000
theorem lowS_zo_104_16_104:Lower true dzo_104_16 roots_104 gzo_104_16 4:=lower_iso_b (d1:=dom_104) (r1:=roots_104) (T1:=gsh_104_16) [(dom_104,16)] (by decide +kernel) (lower_slice_b (T:=gsh_104_16) [] (by decide +kernel) lowS_104)
def dzo_42_4:=0x505000005050
def gzo_42_4:=0x504000004000
def gsh_42_4:=0x50400000400
theorem lowS_zo_42_4_42:Lower true dzo_42_4 roots_42 gzo_42_4 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_4) [(dom_42,4)] (by decide +kernel) (lower_slice_b (T:=gsh_42_4) [] (by decide +kernel) lowS_42)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555400005554000054540000
def gsh_110_16:=0x5555000055540000555400005454
theorem lowS_zo_110_16_104:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x4444000044440000444400004444,0,2),(0x5050000050500000505000005050,0,4)] (by decide +kernel) lowS_104)
def dzo_58_4:=0x5050505050505050
def gzo_58_4:=0x5050504050504000
def gsh_58_4:=0x505050405050400
theorem lowS_zo_58_4_42:Lower true dzo_58_4 roots_58 gzo_58_4 5:=lower_iso_b (d1:=dom_58) (r1:=roots_58) (T1:=gsh_58_4) [(dom_58,4)] (by decide +kernel) (lower_slice_b (T:=gsh_58_4) [(0x505000005050000,0,16)] (by decide +kernel) lowS_42)
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050505050504050504000
def gsh_122_4:=0x5050505050505050505050405050400
theorem lowS_zo_122_4_42:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16),(0x5050505050505050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_108_16:=0x11110000111100001111000011110000
def gzo_108_16:=0x11110000111000001110000010100000
def gsh_108_16:=0x1111000011100000111000001010
theorem lowS_zo_108_16_104:Lower true dzo_108_16 roots_108 gzo_108_16 5:=lower_iso_b (d1:=dom_108) (r1:=roots_108) (T1:=gsh_108_16) [(dom_108,16)] (by decide +kernel) (lower_slice_b (T:=gsh_108_16) [(0x1010000010100000101000001010,0,4)] (by decide +kernel) lowS_104)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,34),(4,20),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,18),(16,20),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(32,96),(36,38),(36,44),(36,52),(36,100),(48,50),(48,52),(48,56),(48,112),(64,68),(64,72),(64,96),(66,70),(66,74),(66,82),(66,98),(80,82),(80,84),(80,88),(80,112)]
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
|4,0=>0xb446e98182
|5,0=>0xce02fc1f5bb661dad64ca7bdb892608524b840ae8223b7b1d02dc1220c600a92207055042be
|6,0=>0xdda88cbf66ba6dca4e1da428c87153826bb8223b7f9977980178730772cd7706a6cd5a6aed16984468cb76144d56b0d521c65061e4bf364b33f4566140ea43e4153da063d5023c07f3b6a43b4ed36da43368b33088306b92f87e2e8d72a4fe2756425032213461e6ac1e6901b5a11b52613dc113c2513bd011d3e0ddcc0c3040756406e440552405234009e0
|7,0=>0xcf622bbb66bb86aa86b2a067796a208b73f8b2417739471d38700a46806f665665e57f541f052da05284b4c50c3d93337e5e361e8330f73047e2ffcc24b621dad30cb1b0a4390a0c3044e001539
|8,0=>0xc90987e995524f4464f438cc63188f25b0e00935
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa00000000aaaaaaaa000000015555555555555555555555540000000088888888888888888800880088008805555555500000000554455440000000000aa00aa00aa00aa008800880088008911111111111111111111111111111112a802a802a802a802a802a802a802a8055555555555555550000000000000000aaaaaaaa88888888aaaaaaaa8888888955555555555555555401540154015402aaaaaaaaa802a80222222222200220055555555550055005555555555005500aaaa0000aaaa0000aaaa0000aaaa000155555555111111115401540110011002828282828282828282828282828282855555555555555554444444444444444
|0,1=>0xaaaaaaaa00000000aaaaaa01555555554141414155555555414141400088008800800080008800880080008111111111111111111111111000000000000000000000000aaaaaaaaaa88aa8911111111111111111111111111111002222000022220000222222222222220000000000005500001111000011550000aaaaaaaaaaaaaaaaaaaaaaaa888888895511551155115511551155115511551000000000000000028a8a8a8a8a828a81111111111111111111111111111110000000000aaaaaaaa00000000aa88aa89555555555555540155551111555510000000000000000002aaaaaaaaa802a8050505050505050505050000050500000
|0,2=>0xaaaaaaaaaaaa0000aaaaaaaaaaaa000155555555555555555555555555115512aaaaaaaaaaaaaaa800000002aaaaa8000005555000055550000555500005500aaaaaaaa22222222aaaaaaaa220022000000000155555554000000015401540000000002aaaaaaa8000000022222222555555555550555055555555555055500000000000000000aaaaaaaaaaa0aaa044444444444444004444444444444402a802a802a802a802a802a8022002200545454545454545454545454545454542222222222002200222222222200220155555555555555555511551155115512aaaaaaa888808882aaaaaaa8888088845454545454445444545454545444544
|0,3=>0x88888888aaaaaaaa88888888aa88aa8955555555554155400000000000000002aaaaaaaaaaaaaaa888888888880088054540000545400005454000054540000aaaa00aaaaaa00aaaaaa00aaaaaa0001555555555555540155555555555554022222222222222002222222222222200000000000055005500000000004400440a0a0a0a0a000a000a0a0a0a0a000a0141400001415400014140000141540002a82aa82aa822a822a82aa82aa822a82555555555555000055005500550000002222222222202220222222222220222155555555555155515555555555515550000000000000000088888888880088055005500555555555500550055445544
|0,4=>0xaaaaaaaaaaaaaaaaaaaa0000aaaa000014141414141414141414000014140002aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa05050505040404040505050504040404aaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a801540154011001100154015401100110888888888080808088888888808080800550055005000500055005500500050aaaaaaaaaa88aa88aaaaaaaaaa88aa8801540154015401540154015401100112aaa8282aaaa82802aaa8282aaaa828000000000000000005555555544444444a2a2a2a2a2a0a2a0a2a2a2a2a2a0a2a0000000000000000000000001551155100002a2a00002a2a00002a2a00002a2a55555555555555555555555555005500
|0,5=>0x2aaaa8282aaaa8282aaaa8282aaaa82855554444555544445555444455554444
|_,_=>0
def sP:Nat→Nat
|0=>0x1e0c481147c40f062408a3a207830c2408a386c7831204508080c10114207831204d081e0c48132207890228c08081c186020021706580881e0c49502287831204a08062408a26207921204508223c189202878312080800838181143418c02285880e0c4810a203830c042840608080
|1=>0x61808a0e3c186120402e1e0c4811420783120452d1010703120400a1e0c48114b042b1e0c4811420783120400a540cb0902289881c0c48100294a7083c189022878312053081e0d281002840f0625201462018c12045082e3c196120440f062408a0a2108f062408a103c1890280508
|2=>0x14f8783120453d103c18902289881e0d101142c40f0624101142020f12f008a103dd8312045081e0c48172207831204538103c4816c2840f06d4481142078312d008a103c1890229988643c189022840f062408a62201a2182408a101c78312045881e0d809022842f062408a542020e
|3=>0x1204508083c18602284471e0cb0902284041e0c48100284040e0c301142020f068808a100c48100289882e3c181151840f8a2408a101220312045081e0c4c302284031204513103c189022a108063030902284041e2408a822200f0624080143818902294881e0c4817e284041e0c481
|4=>0x6e20783122a7088e3c18902284071e0c309022840f062408a16207839a2408a105c7831204508801078312045085e3c18612045081e0cb09020040f062408a98225871e0c4811420783120454a103c1890228e08223c189022840f062408a922140f062408a103c189022a4081e0d116
|5=>0x1e0c4811420783120400a103e78312045081e0c48114207d1062408a107878312045081f4018902284071e0c481142078978045081c3c18612045041f4418902284041f401890228428083c189022840f0624080142c40fa00c30902284171e0c48100284041e0c4a4022840f062408a
|6=>0x3c1890228404
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd77741dc9770d9bc76d5daf66a1da17669d937631d8575f9d7775c1d697589d5b7551d4e651dd4164e9d3374b1d257479d177441d097409cfc63d5cee739dce07365cd2732dcc472f5cb672c18a97289c9c6255c8e721dc8071e5c7271adc647
|7,0=>0x2c46af5eb58ab62a58a762958a3628589f9e7869c5e698989e5b7951e4c891223d78d9e2e889de207865e12782de0477f21f577b61e58
|8,0=>0xbe9ef37bb1ee66b7ded87b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 82 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c291e210c3f12215020080544272c210e1812211e29069002291e251c277428080d1e250802142106df08071e255e1812210e25120214211e0214211e1a12211e2512211e211e1a12211e8a2c211029502308052e241e011421082b1e25443c2c2112291c291e2108001e2514213c5b12290e1812211e291c291e2108001029
|1=>0x12211e01142102291e2508071e259e0706210e251e2912211e29120214212c0512290e211e2908211e251e0d1221142112290e071e290e051e290e271e291c2b1e2108231e253c2b1e0508051e253c271e052c211229123d12212c3d12291e2514212c211229443f12010e211e290e231e291e880c290692022908211e252e3f
|2=>0x1e251421062106051e0506291e29480c022912211e211e2506051e25062908051e25120214210629
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x43000000000000022000000000000000000000000002
|6,0=>0x4d24b24920004720000000004524324123e33c23a20000003823533233112e32c22930002720002610000002422222021d30000000000000000001b21921811620001331120e30c2093000000000072000000
|7,0=>0x8b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f2
|8,0=>0x9319219110009018f18e18d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x3718703508702718702708b02708701010500f087009023009003006116006006005087004019004007004003001881001087001086001000000886000600000105000080000060000019000007000006000005000004000002000001000000
|1=>0x82f88780900244900228588720088320080313508f11000d1070871060161050871041120cf0870ad0870a5a8708f0e708f087049061
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5000000080000000000003
|6,0=>0x30420020000020812810800071572d008e0030080000c22550000000000410c200434609200000d000
|7,0=>0x195b0b6f46c698864ad16e27e631c86079da658654e8a92
|8,0=>0x9db8cfc61b9e
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 24 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_118 7 roots_118 ops++addP pm 2 dom_94 7 roots_94 ops++addP pm 3 dom_116 4 roots_116 ops++addP pm 4 dom_54 4 roots_54 ops++addP pm 5 dom_104 4 roots_104 ops++addP pm 6 dzo_104_16 4 roots_104 ops++addP pm 7 dom_110 7 roots_110 ops++addP pm 8 dom_30 4 roots_30 ops++addP pm 9 dom_42 4 roots_42 ops++addP pm 10 dzo_42_4 4 roots_42 ops++addP pm 11 dzo_110_16 6 roots_110 ops++addP pm 12 dom_122 7 roots_122 ops++addP pm 13 dzo_58_4 5 roots_58 ops++addP pm 14 dom_62 7 roots_62 ops++addP pm 15 dzo_122_4 6 roots_122 ops++addP pm 16 dom_92 4 roots_92 ops++addP pm 17 dzo_108_16 5 roots_108 ops++addP pm 18 dom_90 4 roots_90 ops++addP pm 19 dzo_106_4 5 roots_106 ops++addP pm 20 dom_86 4 roots_86 ops++addP pm 21 dom_108 5 roots_108 ops++addP pm 22 dom_114 4 roots_114 ops++addP pm 23 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_104_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_42_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_110_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_58_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_122_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_108_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_106_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 7:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_186
def dzo_200_16:=0x1010000000000000101000000000000010100000000000001010000
def gzo_200_16:=0x1010000000000000100000000000000010000000000000000000000
def gsh_200_16:=0x101000000000000010000000000000001000000000000000000
theorem lowS_zo_200_16_200:Lower true dzo_200_16 roots_200 gzo_200_16 4:=lower_iso_b (d1:=dom_200) (r1:=roots_200) (T1:=gsh_200_16) [(dom_200,16)] (by decide +kernel) (lower_slice_b (T:=gsh_200_16) [] (by decide +kernel) lowS_200)
def dzo_204_16:=0x11110000000000001111000000000000111100000000000011110000
def gzo_204_16:=0x11110000000000001110000000000000111000000000000010100000
def gsh_204_16:=0x1111000000000000111000000000000011100000000000001010
theorem lowS_zo_204_16_200:Lower true dzo_204_16 roots_204 gzo_204_16 5:=lower_iso_b (d1:=dom_204) (r1:=roots_204) (T1:=gsh_204_16) [(dom_204,16)] (by decide +kernel) (lower_slice_b (T:=gsh_204_16) [(0x1010000000000000101000000000000010100000000000001010,0,4)] (by decide +kernel) lowS_200)
def dzo_206_16:=0x55550000000000005555000000000000555500000000000055550000
def gzo_206_16:=0x55550000000000005554000000000000555400000000000054540000
def gsh_206_16:=0x5555000000000000555400000000000055540000000000005454
theorem lowS_zo_206_16_200:Lower true dzo_206_16 roots_206 gzo_206_16 6:=lower_iso_b (d1:=dom_206) (r1:=roots_206) (T1:=gsh_206_16) [(dom_206,16)] (by decide +kernel) (lower_slice_b (T:=gsh_206_16) [(0x4444000000000000444400000000000044440000000000004444,0,2),(0x5050000000000000505000000000000050500000000000005050,0,4)] (by decide +kernel) lowS_200)
def dzo_202_16:=0x5050000000000000505000000000000050500000000000005050000
def gzo_202_16:=0x5050000000000000504000000000000050400000000000004040000
def gsh_202_16:=0x505000000000000050400000000000005040000000000000404
theorem lowS_zo_202_16_200:Lower true dzo_202_16 roots_202 gzo_202_16 5:=lower_iso_b (d1:=dom_202) (r1:=roots_202) (T1:=gsh_202_16) [(dom_202,16)] (by decide +kernel) (lower_slice_b (T:=gsh_202_16) [(0x404000000000000040400000000000004040000000000000404,0,2)] (by decide +kernel) lowS_200)
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,28),(12,76),(12,140),(16,18),(16,20),(24,26),(24,28),(24,88),(24,152),(64,68),(64,72),(64,192),(66,70),(66,74),(66,82),(66,194),(80,82),(80,84),(80,88),(80,208),(128,130),(128,132),(128,136),(128,192),(144,146),(144,148),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|4=>11
|5=>96
|6=>287
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x885688806a74ad360cc14b5d649bf544c5a41b79311aa2e2e81d90e
|5,0=>0xfc268f901ef8b20f4311eb64ee0c4cddc9fdd7a1d369dd2c07d26d5cf275ccb87ca20ac9a62c8ab7c7577c6e56c04e1baf9cb95f0b4dbfb3f0fb19daaccdba2c42a0d0da0ad09fb4b9b9d99a92699f0598e539307f90cd18ef3187dea87b1d85dc48557e83736836a87f1727c42878fe178e417428372ce97261771b9a713a970ea26d0bd6d05f659fb62f776222562163613845d95a5502c53f085073c4fc514b8a646aa1436c73eca93ceab3a9b6373fc33a8731a022b00b28fe7282af24a822396d209261fc211e59f199be163b3162720fd350df040d95e0c978080bc06e3605b57019e000a71009aa0077d00201
|6,0=>0x4948947ecf47df3479e9476f24647a46098459da45568449324469b435fb4336f41d6c40d8540ca340b33409d43f9dd3f7fb3f6d63f3473eca93c7363c25c3b2903a4153a01539b08398493966f38c3938892388913796d377e9375be370cf36f24368cc3638335dc835ad7349633468533d9e33824327ed31c1f311323098e2db322d2ee2c8692c52a2c4452c06b2c0682bdcd2b6d62b0122ad1129c0a299e92975926b7126b2125fba25d2924f0e24eb824d2a24cf4249b4249ac23b0c23a87225fe225612137a205ac201151fed31e9af1e99d1da611cac71c58d1c27a19c8518bb3187a9187a51837017f50179f81620b15feb15c18159ce133b81334412c5311951107480f4d00f4490e8c70dd390db9d0d74c0d6300cf570cd170b9cb0a09009c4809aae093c108cde0609a05a190581b0464a03f72037e7005d600208
|6,1=>0xba0a7b9079b795cb6f01b5d0ab4dbfb4c17b3c80b10bcb0aa3aec2eada97a9c46a963fa5e06a443da43bea4121a3eb9a3555a2d0fa2d06a13f3a12c99ed419d5959d43c9cee29bf799b9d99b2529b1209a5ac99df6990ae98e539755a96de1969de935ec92e989291e924148fffa8e8c38e4498e3238dd448d4508d29d8cb338a5d5890818902a86b848629885dc48513484ab2839e881cb581b6a8173d804747eca07e2237e0337d9e67d94a7d9327cc1f7c4c87ba0a7b6ae7b5607aa11796b5794b178a9c7890a784587815e7616775be1745be73ad37373070ea270c57702a86d30b6aee46a923697f16919d63e7963b806388062789604e55fc6d5f5025f0625e0f65d9b85d7f35cb455c6355c28a5b23f5ae7758ca9580f8572a25711755eb455bf7556645228a5154250e94508344d9aa4c5c94c44b4c3ce49e1749546
|6,2=>0xf9851f9336f6557f144aee58aee0fce4980e2f31e1c75dcea4d86ecd613ad5fdbd1b85d0b5dce578ce07acba3dca5a9c9feac99bac901cc7d4ec6a9ec40a0c3ecbc1bdcc127dbfdf3bf403bb6d8
|7,0=>0xf2cccee58ae898de1901ce4b1cc4e2c860dc83fac3ecbc3208c16a0c1657c061bbf4a0b69f0b3329b0761b0144a9c46a870fa5b37a59a4a4bfb9ad4c9a5ff962ab94d2494cae9102c90a308e7178b00489af4894d58887284ebc807497d3217bdee7b5607a0eb7955a794e677a497660b75b23756fe71f6b6f28f6ee70686dc671976672264c076476063d46610ac5ede65ca115c7d45bf235b9875966756fd5567d855d835413050ee24e3f64b6a54a5a8495c0485c74814c4657945e6644e7e43aa3422ed410993e10d3c0a43a41538cae35d893456c320f631f9731a94316382fabf2f65c2f2eb2c07229be227669272bc26de4269ae2680924f0e24d2a244582181620532202ee1cad11c8fc1c5e516d2b15cb8159be156da149d8117b8110a80e24c0d29d0cc540be1a0aa1e0a81309821090af054ff048520426d027cf
|7,1=>0xf9e30f56ee
|8,0=>0xc5345bf4a0bebcebad5ea382584d9378bdf5a519577e145e2a379622b7a22b37d2426a205e810d810c457050df
|9,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00000000aa00aa0155115510000000015511551000000001551155100000000155115512828282800000000282828280000000028282828000000002828282855555555000000004444444400000000550055000000000044004400aaa0aaa0000000008880888000000000aaa0aaa0000000008880888155555554000000015555555400000000000000000000000000000002aaaaaaa800000002a802a80000000002aaaaaaa800000002a802a8055555555000000005555555500000000505050500000000050505050aaa0aaa000000000aaa0aaa000000000aaa0aaa0000000000000000151515150000000015151515000000001515151500000000151515152aaaaaaa80000000222222220000000028282828000000002020202055550000000000005555000000000000555500000000000055550000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0155555554000000015151515000000001554155400000000151415142222222200000000222222220000000022222222000000002222222255555555000000005555555500000000555555550000000000000000
|0,1=>0xaaaaaaaa000000000000000000000000aaa8aaa9414141400000000141414140000000015555555400000001554155408888888800000000888888880000000088888888000000008888880000000000000000055505550000000000000000000000000555055500000000000000000a2a2a2a2000000000000000000000000a2a0a2a154015400000000000000000000000001540154000000000000000002aaaaaaa800000002aaaaaaa8000000022222222000000002222222200550055000000000044004400000000005500550000000000440044aa00aa0000000000aa00aa0000000000aa00aa0000000000880088000000000000000000000000000000000155555554000000015401540002a802a800000002a802a8000000000002a802a800000002a802a8055555555000000005555555500000000555500000000000055550000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa155555554000000015401540000000001414141400000000140014002aaaaaaa8000000000000000000000002aaaaaaa800000000000000055555555000000005555555500000000555555000000000055550000
|0,2=>0xa000a00000000000a000a00000000000a000a00000000000a000a0155555540000000015555554000000001555555400000000155540002aaaaaaa8000000002800280000000002aaaaaaa80000000028002805555555500000000444444440000000055555555000000004444444400aa00aa0000000000aa00aa0000000000880088000000000088008801540154000000000000000000000000015401540000000000000000282828280000000028002800000000002828282800000000280028055445544000000005544554400000000554455440000000044444444aaaaaaaa00000000aaaaaaaa00000000aa00aa0000000000aa00aa01555555540000000154015400000000011111111000000001100110028282828000000002aa82aa80000000028282828000000002aa82aa800000000000000005555555500000000000000000000000050505050aaaaaaaa00000000aaaaaaaa00000000aa00aaaa000000000000000141414140000000015555555400000001010101000000000111111112aaaaaaa800000002aaaaaaa800000002aa82aa8000000002aa82aa855555555000000005050505000000000555555550000000050505050
|0,3=>0xaaaa000000000000aaaa000000000000aaaa002200000000aaaa000155115510000000011111111000000001551155540000000111111112aaaaaaa800000002aaaaaaa8000000022220000000000002aaa8000555555550000000055445544000000005555555500000000554455440000000000000000aaaaaaaa000000000000000000000000a2a0a2a044004400000000004400440000000000440044000000000044004402aaaaaaa8000000008800880000000002aaaaaaa80000000088008805555555500000000555555550000000055555555000000005500550000aa00aa00000000aaaaaaaa0000000000aa00aa00000000aa00aa0155555554000000015151515000000001555555540000000151515152aa82aa8000000002aa82aa80000000022202220000000002220222055555555000000000000000000000000555055500000000000000000aa00aa0000000000aaaaaaaa00000000aa00aa0000000000aaa0aaa00000000000000001540154000000000000000000000000015401540002a802a80000000002a802a80000000002a802a800000000022002200040004000000000004000400000000000400040000000044444444
|0,4=>0xaaaaaaaa00000000aaa8aaa955555400000000015554000000000001555554000000000155541402aa22aa2000000002aaaaaaa800000002aa20000000000002aaa800055005500000000005500550000000000550055000000000054005400aaaaaaaa00000000aa00aa0000000000aaaaaaaa00000000a000a00000000000000000000000000000000001555555540000000155115510282800280000000028280028000000002828002800000000282800055555555000000005555555500000000550055000000000000000000aaaaaaaa00000000aaaaaaaa00000000aaaa000000000000aaaa0a0155555554000000015541554000000001555555540000000155415542aaa8000000000002aaa8282800000002aaa8000000000002aaa8280550055000000000055005500000000005500550000000000500050008a008a00000000008a008a00000000008a008a0000000000880088015555555400000001555155500000000000000000000000000000000222222220000000022222222000000002aaaaaaa800000002222222200000000000000000000000000000000555555550000000005000500
|0,5=>0x8888888800000000888888880000000088aa88aa000000008888888844444444000000004400440000000000444444440000000044004400000000000000000000000000000000008888888800000000000000055555555000000005555555500000000555555550000000044444444aaaaaaaa00000000aaaaaaaa0000000000aa00aa00000000aa00aa0155555554000000015555555400000000000000000000000001540000000000000000000000000000000000008888888800000000880088000550055000000000000000000000000005500550000000055005500aaaaaaaa00000000aaaaaaaa0000000022222222000000000000000001540154000000000154015400000000014001400000000001400142aaaaaaa800000002aaaaaaa800000002aaa8888800000002aaa80001505150500000000110011000000000015051505000000001100110000000000000000000000000000000000aaaaaaaa000000002200220154015400000000015401540000000001140114000000000110011002aaaaaaa8000000022222222000000002aa22aa2000000002222222205050505000000000505050500000000050005000000000005000500
|0,6=>0xa000a00000000000aa00aa0000000000a000a00000000000aa00aa01555400440000000155540000000000015554004400000001555400008800880000000000880088000000000088888888000000008800880000055000000000000005500000000000000550000000000000055002222222200000000000000000000000022222222000000000000000044404440000000004440444000000000444044400000000044404442aaaaaaa8000000008880888000000002aaaaaaa800000000888088805050505000000000000000000000000050505050000000000000000aa22aa2200000000aa22aa2200000000aa22aa2200000000aa00aa0000000000000000015555555400000000000000000000000155415540000000000000000000000000000000002800280000000000280028055550000000000005555000000000000505500000000000050550000222222220000000022222222000000002222222200000000000000015555540000000001555554000000000155555400000000015555540002a802a80000000002a802a80000000002a802a800000000000000000000000000000000055005500000000000000000000000000550000
|0,7=>0xaaaaaaaa00000000aaaaaaaa00000000a000a00000000000aa00aa0155515550000000015551555000000001555155500000000155515550080808080000000008080808000000000808080800000000000000000000000000000000000000000000000555555550000000000000000a2a2a2a200000000a2a2a2a200000000a2a2a2a200000000a0a0a0a000000000000000000000000000000001540154000000000154015400888888880000000088888888000000008888888800000000880088055551111000000005555111100000000555511110000000055550000a0aaa0aa00000000a0aaa0aa00000000a0aa000000000000a0aa000000000000000000001400140000000000000000000000000014001402aaaaaaa800000002a802a80000000002aaa8000000000002a8000005555555500000000555555550000000005000500000000000500050000aa00aa00000000000000000000000000aaaaaa000000000000000155555554000000000000000000000001551155100000000000000002aaa8888800000002aaa8000000000002aaa8888800000002aaa800000000000000000000000000000000000555055500000000055505550
|0,8=>0xaaaa000000000000aaaa000000000000aaaa0a0000000000aaaa0a01111111100000000155555554000000011001100000000001540154028a828a80000000028a828a80000000028a828a80000000028a828a844444444000000005555555500000000444444440000000055445544aaaaaaaa00000000aa00aa0000000000aa88aa8800000000aa00aa0155540000000000015555555400000001555400000000000155555402aaa8000000000002aaaaaaa800000002a800000000000002a802a805555555500000000555555550000000005050505000000000000000000aa00aa0000000000aa00aa0000000000aa00000000000000aa000154015400000000000000000000000001540155540000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaa8011111111000000001111111100000000101010100000000010101010aaaaaaaa000000002222222200000000aaaaaaaa000000002020202000000000000000000000000000000001115511540000000000000000000000000000000000000000000000002828282800000000202020250555055000000005054505400000000505550550000000050545054
|0,9=>0xaaaa0000000000000000000000000000aaaa00000000000000015401555400000001540154000000000154015554000000015401540088008800000000008800880000000002aaaaaaa80000000088008800505050500000000050405040000000005050505000000000504050400000000000000000000000000000000aaaaaaaa00000000aaa0aaa001540154000000015555555400000000015400000000000155540000000000000000000000000000000000000000000000000002aa82aa855555555000000000505050500000000555555550000000004040404aaaaaaaa00000000aaaaaaaa00000000aaaaaa0000000000aaaaaa0044444444000000004444444400000000444444000000000044444402a802a80000000002a802a80000000002a800000000000002a800000555555550000000055005500000000005555555500000000550000008888000000000000aaaa0000000000008888000000000000aaaa000000000000000000004444444400000000000000000000000040404042aaaaaaa800000002aaaaaaa80000000002a802a800000000000000055555555000000000055005500000000555555550000000000550000
|0,10=>0xaa22aa2200000000aa00aa0000000000aa22aa2200000000aa00aa0155555554000000015555555400000001555555540000000044004402aaaaaaa800000002aaaaaaa8000000008880888000000000888088855555555000000000055005500000000505050500000000000500050aaaa000000000000aaaa000000000000aaaaaaaa00000000aaaaaa0014141414000000001414141400000000141414140000000000000002aaaaaaa800000002aaaaaaa800000002aa22aa2000000002aa22aa200000000000000000000000000000000001100110000000000000000aaaaaaaa000000000000000000000000aaaaaaaa00000000aa00aa01555555540000000000000000000000011111111000000000000000000088008800000000000000000000000000880088000000000000000550055000000000055005500000000005511551100000000550055008a8a8a8a0000000088888888000000008a8a8a8a000000008888888800140014000000000010001000000000001400140000000000100012aa22aa20000000022222222000000002aa22aa2000000002222222255555555000000001111111100000000555555550000000011001100
|0,11=>0xaa00aa0000000000aa00aa0000000000aa00aa000000000000000000015400000000000001540000000000000154000000000001555400000088008800000000008800880000000000880088000000000000000110111010000000011001100000000001101110100000000110011000000000000000000aaa8aaa8000000000000000000000000aaa8aaa911551154000000000000000000000001115511540000000000000002a2a0000000000002a2a0000000000002a2a0000000000002a2a000055555555000000005555555500000000545400000000000054540000aa00aa0000000000aaaaaaaa00000000aa00aa0000000000aa88aa8800000000000000000154015400000000000000000000000001400140008800880000000000880088000000000080008000000000008000855555555000000000000000000000000550055000000000000000000aaaaaaaa00000000aaaa000000000000aaaaaa0000000000aaaa00000000000000000000000000000000000000000000000000015401540222aa22a800000002222222200000000222aa22a800000002222222200550055000000000055005500000000005500550000000000500050
|0,12=>0xaaaaaaaa00000000aaaaaaaa0000000000220022000000000000000141554154000000014155415400000001415141500000000141514152a802a80000000002aaaaaaa800000002a800000000000002aaa800055505550000000005550555000000000555055500000000050505050a0a0a0a000000000aaaaaaaa00000000a0a0a0a000000000aaa0aaa145454544000000014541454000000001454545440000000145414542aaaaaaa800000002aaaaa80000000002aaaaaaa800000002aaaaa80000000000000000000000000000000005555555500000000555555000000aaaa000000000000aaaa000000000000aaaa000000000000aa0000000000000000000000000000000000000155540000000000015402aaaaaaa800000002aaaaaaa8000000022a2a2a2800000002222222255555555000000000000000000000000555555550000000055505550aa0aaa0a00000000aa00aa0000000000aa0aaa0a00000000aa00aa0000000000000000004444444400000000000000000000000044004400282828280000000020202020000000002828282800000000202020255555555000000005555555500000000555555550000000055445544
|0,13=>0x2222222200000000222222220000000022202220000000002220222155555554000000015555555400000000000000000000000154015400080808080000000008000800000000000808080800000000080008000550000000000005555000000000000005500000000000055550000aaaaaaaa00000000aaaaaaaa0000000000aa000000000000aaaa0001555555540000000155555554000000001414141400000000140014000000000000000000000000000000000002a802a800000000000000055005500000000005500550000000000555555550000000055005500aaaaaaaa00000000aaaaaaaa000000000000a8a8000000000000a8a95555555400000001555555540000000000000000000000015541554000000000000000000000000000000002aaaaaaa800000002a2a2a2a1111111100000000111111110000000011111111000000001010101000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00015555555400000000000155540000000155555554000000000001540282828280000000028282828000000002aaaaaaa800000002a2a2a2a55550000000000005555000000000000555511110000000055550000
|0,14=>0xaa00aaaa00000000aa00aa0141414140000000015555555400000001400140000000000154015402aaaaaaa8000000028a828a8000000002aaaaaaa8000000028a828a80000000000000000555555550000000000000000000000005454545400a000a000000000a0a0a0a00000000000a000a000000000a0a0a0a111115554000000011111111000000001111155540000000111111112aaaaaaa800000002aaaaaaa80000000222aa22a80000000222222220000000000000000505050500000000000500050000000005050505088aa88aa0000000088aa88aa0000000088a888a80000000088a888a911111110000000000000000000000001115511540000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002a2a2a2a555555550000000055555555000000005511551100000000550055000000000000000000aaaaaaaa0000000000000000000000008888888941400000000000014140000000000001415400000000000141540000028002800000000002800280000000000280028000000002828282800005454000000000000545400000000000054540000000000005454
|0,15=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000a0a0a0a155541400000000015554140000000001555414000000000155541402a802a80000000002a802a800000000028002800000000002800280005050505000000000505050500000000040404040000000004040404aaaaaaaa00000000aaaa000000000000aaaaaaaa00000000aaaa0001555555540000000155555554000000015151515000000001515151500002aaa8000000000002a800000000000002aaa8000000000002a8055555555000000005555555500000000000055550000000000005500a2a2a2a200000000a2a2a2a200000000a2a0a2a000000000a2a0a2a155555554000000015551555000000001555555540000000155515552aaaaaaa800000002aaaaaaa8000000000002aaa800000000000000055555555000000005555555500000000550055550000000055005500aa00aa00000000000000000000000000aa22aa22000000000000000155115510000000015511551000000001555555540000000155115512aaaaaaa800000002aaaaaaa8000000000002a800000000000002a8055555555000000005555555500000000110011000000000011001100
|1,0=>0xaaaaaa0000000000aaaa000000000000aaaaaa0000000000aaaa000155551110000000015555111000000001555511100000000155551112aa82aa80000000028282828000000002aa82aa8000000002828282850505050000000005050505000000000555055500000000055505550aa00aa0000000000aa00aa00000000000000000000000000aa00aa00015401540000000155555554000000000000000000000000000000022220000000000002222222200000000222200000000000022222222000000000000000055555555000000000000000000000000555500000000aaaa000000000000aaaa000000000000aaaa00000000000000000000000000000000000000000000000155540000000000015554000000000000000000000000000000000002aaaaaaa800000002222222211111111000000001111111100000000110011000000000011001100
|_,_=>0
def sP:Nat→Nat
|0=>0x5050060d0084446040181844110501042031000400040f80c1a01050503c03068042204018343a1105010380d00860141401834240108810061b068041414048541a0105050060d0c8602204030342e1105050120f0680428150783402140b0541a010204c2401000502612008442009078340204070341800020240c0b0501012080081c0803030140004018080200
|1=>0x6804160a020241a010602808031b02002000204c1206160280803030d4220a0200c1a011a0280803068040a00020cc640d00828280d0c80462110200c1a01060000803068c0220a0a03432010b8442816068045e110a024060d160645c0306804220a0209c1a0116800080d160ac540a0209c1a01148000803100040e0a0209c1a28088104e0d0089822041280c4801
|2=>0x2280c1a0108828081322004220a0203402430882808030680422420a0242c0d008682803069043211020384e0d1600028030680480111f80c1a01088282803068f8220a020244e0d008007a03068640211020f04e0d0c84408030302c220a0200c760d0082828130b03402110209c1a011c80008091b834020a0200c04010882808030400422070a0940608008440809
|3=>0x948220a020242c0d00920080306944220a020241a0128000084f018340211080241a0124138060d00844140409848021105134060d0084414041c0541a01050101a0118844140426034021105010264b0084414140b00c1a01088102609040040004108241a010001070090680490142500c1a010881006012484414040483402482380c1a01088280846138340200
|4=>0x5050120d008681404018181a5c0882828150680414040496c1a0105010b61506804141401834025a08850120d00920280306804b211020241e0d00828081507834020a02024b00d008280803030205800020244e0d0095c2813190200211020241e0d0092008160a834020a0200c40012b000aa030686402110200c0c540882828460182002110a00c1a0129844080d
|5=>0x34844140401818321134028086701834021105010266601834020a01990100d0084414041980c1a01088280809018348201050104e03068042263310101a0108984141401834026008828080310004ac1105010060d2f804220a0200c100d008d014040480c1a2c2f02808460180452110501006060400400110204c4e0d0c80422040480c1a012e8280813048340200
|6=>0x500cee0d0084414140183402760882808033a834021105010120d009d0220a0a00c1a01089cc140401834021139028e22701834021105010e00906804220a0a00c1a011c8441404018340253088282803378340211051b8060d00844140401834026d088280803030205811050101a0136044c20a0204c060114844141401834021124010700306804d60a0200c1a01
|7=>0x68045e0008850120306804220a0200d000d008441414018343201088a8081319020021105010067f06804220a021f8060d160441404108c81a0108828080306804227d050100606068e4220a0200c1a011c9f01404019ec1a0108828087a068045211050104e030697002110200c1a013c844147801834021105010060d00888220a02118060800844141419034022a
|8=>0x200d1a200084414044600c1a0108828088b01834021105228080306804220a0203458010b844140401a241a0108828080303004228805010060d008e4000a0a00c1a5c0c8042214018340211430290a0401834021105010060d00a0c220a020242c270680422140700c1a2c088280803068042282050104e0d00978220a0200c1a014084414041080c1a01088280827
|9=>0x1834021105010060d00a60220a0200c1a9608828284601834021105050069406804220a1e80c1a0108828083c13834021105010060d00964220a021984e030680414041380c1a01001a0080306805241105010060d16005220a0a02406080680422040183402900882808031b03432110523c060d0084414040700c1a2c3e028080347034021105010260d00860220a
|10=>0x2402808030680400a505010122706804001102290060d008441414098c81a0108828080306a8c321105010060d00a88220a0a00c1aa108828080306804680a020e02c030680422040700c1a2c00028080306805401105010120306804000a022784e0d0084414040b00c1a01358280803068053a1105010060d00a70220a0226c060d0084414144d00c1a01088280899
|11=>0x50101c270686422040183402b00882828af01834021105010060d00ab8220a0202406080680400040183402ad08828080306805581105010063206890020a022a4060d1604414ab0200c1a010882828a901834320108810060600845540a0200c1a0108aa0140409a9c1a01088280803068b14c0a019901a01088280803030345800050101c0306904220a020241a01
|12=>0xf00c1a010882808bb01834021105010060d00801740a01ae01a01088280870018180211050116e0306804220a0200c1a015b044141401880100108810060d00ad4220a0200c1a120084414040183432180882808213300c1a01050102609068b0020a0200c1a011a84414b30183402110501026b206804220a020944e0d0084414041080c400108828280306ac40211
|13=>0x80014040489c1a0100010060d0095800110a024060d009ac14041380c400d0080028030686402112e8102603030b0220a0200c1a016104414040183432c108828080d2e0042e1105010260312004220a02300060d0084414be01834021105010060d008457a0a0209c1a011484414045780c1a010002808030300452110501026270680400110200c1a015e0441404
|14=>0xb09c060d00844080366034021105011960306804220a0200d940d008441404018201a013a0459004018340211050114e0306804220a4d00c1a0108828081304818021105010060d00b1c220a0200c1a01630441404018358a0108828087e13834021105010fc0306864220a020704e0d0084414046200c1a0108828080306804161105010060d00830220a0230c060d
|15=>0x6804220a0203432011884414040183402d408828080306805a611050104e0306804680a0200c1a0169044140401b441a010882808090680490d00183432010882808030680422cf050108c7a06804220a020241a015f8280827018352c110501006ce06804220a0204c062000800140413834026a0882828cd01834021105050067506804220a02024060d160641404
|16=>0x183402110501012150680414040980c028408828280306804bc1105050060d00a40220a0a058060d0084408030300400680501006061d044d00a020541a0105010060d00b68220a021c00620008441455018340211050104e320680400110200c1a2c0098414046c09c1a010882808030689058010500c1a016b84414046b00c1a010882808036a8340211050102638
|17=>0x501006e8008441404018340211240104a0304004220a0200c1ae700844140401834021173028080306804c0110501006e506804220a020e0120d0086814047200c1a0108828080303035c6110500dc40d00844140401b8402110500d700d00844120306805c0110505012160183402110200c1a016f844140401b781a0100044080306805ba11050101a011884414db
|18=>0x7900c1a0108828080901834b80105010700306804220a0200c1a017880022040183402f000044083c01834020005011de0306804220a02198060d00844140401bb81a0108828080376834021105010261606804220a0204c060800800220401bb01a0108828080306944220a0200c1a01002d0280375804220a02024060d0098c14041380c1aea08828080306ba40211
|19=>0x1834021105050260906804220a1380c1a0170044140401834501105040060d00844140401bdc1a010882808f601834021105010060d00950220a022bc4e0d0084414140980c100108840060d008449004048581a010d02808f401834021105010060d00845e60a020241a0117800141401834021808828080306904321105010060d51804000a0200c1a01200441404
|20=>0x6804220a0200c1afd0084414041c09c060d00844140401b781a01088292e0401834021105010060d00bf0220a02024060d009ac14fb0209c060d0084414040489c060d00844141401834022f08828081301880021105010068d06804220a0200c1a01328441404138c81a010882808037d034581105010060d00be0220a0209c060d00844ae1402058060d008440816
|21=>0x50102627018340211050104e0d008e8220a0200df40806804220a02084060d0084414140480c1a0108828280306804221a050100608068b0021105050060d00a1c220a0209c060d00844d60a0200c0c0d0c8441404018343201089a014040181802113402808030680422d9050101c2706804220a02038060d0c844140401bfc100d008441404018201a0100045fc03
|22=>0x18d81a0108828080306804230305408120306804220a02024060d0080014040480c1a012f0441404019e81a01089a0140401834025e08828080306805c61105010060d00bc4220a0200c1b010084414040183402f0088280809018181a0108828280304034021102024060d009f0140401834b82c008441404018340300088280813018340200088280813018200211
|23=>0x800220a8104c060d0084414970209c060d0084414041380c1a0108a7c140401834580115028080310034320108828080306804006b0501006eb00844140401bfc1a010882992040480c1a0108828083c0480c1a0108828089e01834021105010060d00940220a0a00d2a0d0084414c90200c1a0108828083c01834021105012080306804220a0a04c060d008441404
|24=>0x5050063206804220a0209c060d00844d00a0209c060606804220a0200c1a011684414041089c060d0084414040700c1a010004414035c834021105010060d00844ae0a0200c1aea08828080306804224805010060d00860220a02038060d00844f80a0209c060d00845b20a02094060d008441404018360a110501006fa06804220a02024060d16004220a0200c640d
|25=>0x18340200088101c0306804226805050060d00844d00a85010060d00800220a0204cf40d00844140401c240211050501c0306804220a02024060806804220a0204c120d0084414048400c1a010882808030697032010882828040480c1a01088280803838340211050114e0306804220a0200c1a1900844540a0200c1a0108c180813018345801088280803068058211
|26=>0x8828083801834021105010060d00844c20a6e00c1a0108828080306890021105010060d0c804225d05010120306804220a020c81a0115028080306804ec1105010060d008e4220a0200cde0d00844140401834021124010fc1301834021105010060d008457e0a0200c1a011d044d00a8580c1a0108828080906804340a0183402e00882808037f8340200088280827
|27=>0x882a040306804220a0200c1a01089a01404018181a0108828080e01834021105050060d008441404018c81a0108828080306804229f050104e0306804220a02024060d00be4220a0200c1a017c844140404858060d0084414040b00c1a0108829260306804220a020f0060d16004220a0204c4e0d0084414040700c400d0084414041c024060d008441404018181a2c
|28=>0x401834021105010067a06804220a02024060d0084414040183402110d028080306804220a0200c1a01178441404018201a0108828280401834021105188080306804220a0200c1a2c00844150a0200c1a01
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1af61a961a3619d61976191618c51866180617a6174616e61686162615c61566150614a6144613e61386132612c61266120611a6114610e6108610260fc60f660f060ea60e460de60d860d260cc60c660c060ba60b460ae60a860a2609c60966090608b5085607f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26d52676261625b62565250624a6244623e62386232622c62266220621a6214620e6208620261fc61f661f061ea61e461df51d961d361cd61c761c161bb61b56
|6,0=>0x425741e741774107409740273fb73f473ed73e673df73d873d173ca73c373bc73b573ae73a773a073997393638c7385737f63796372736b7364735d7356734f73487341733a7333732d6326731f73187311730b630472fd72f672ef72e872e172da72d372cc72c572be72b772b072a972a2729b7294728d7286727f727962727
|6,1=>0x5dd75d675cf75c875c175ba75b375ac75a5759e75986592658b7584757e6577757075697562755b7554754e65486541753a7533752c7525751e751775107509750274fb74f474ee64e774e074da64d374cc74c574be74b774b074a974a2749b7495648e7487748074797472746b7464745d7456744f74487441743a7433742c7
|6,2=>0x796778f77887781777a7773776c7765775e77577750774a6743773c7735772e7727772077197712770b770476fd76f766f076e976e276db76d476cd76c676bf76b876b176ab66a4769d7696768f76887681767a7673766c7666665f76587651764b6644763d7636762f76287621761b6614760d760675ff75f965f275eb75e47
|6,3=>0x942793b7934792d79267920691a6914690d790678ff78f968f368ec78e578de78d778d078c978c278bb78b568af68aa58a3789c7895788e78877881687b6875686e78677860785a6853784c7847584078397833682c7825781e78177811680a780377fc77f577ee77e777e077d977d277cd57c677bf77b877b267ab77a4779d7
|6,4=>0xa177a107a097a0279fb79f479ed79e769e169da79d379cc79c579bf69b969b279ab79a4799d7996798f79887981797a7973796c7965795e7957795079497
|7,0=>0xbe58bde7bd68bcf7bc96bc27bba8bb28bab7ba47b9d7b967b8f7b887b817b7a7b737b6c7b657b5d8b558b4e7b477b407b397b327b2a8b246b1d7b158b0e7b068aff7af78af07ae88ae17ada7ad37acb8ac47abc8ab57aad8aa67a9f7a987a917a898a827a7c6a757a6d8a667a5f7a587a517a498a418a3a7a337a2c7a257a1e7
|7,1=>0xdb18daa7da46d9c8d957d8d8d858d7e7d777d707d6a6d637d5b8d547d4e6d477d407d397d336d2b8d247d1c8d166d106d0a6d028cfb7cf38cec7ce48cdd7cd76cd07cc88cc17cba7cb28caa8ca37c9c7c948c8e6c868c7f7c787c708c688c617c598c518c4b6c447c3e6c377c307c288c208c197c136c0c7c048bfc8bf57bed8
|7,2=>0xdc08db97
|8,0=>0xe3c7e357e2e7e286e217e1a7e137e0c7e057dfe7df86df17dea7de37ddd6dd67dcf7dc87
|9,0=>0xe436
|_,_=>0
def wAt:=mkWire dB 268 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1844190a9018460880e020290d0290184501844049230184501844190a9018460880e0882900845049230184501844048350184501845021210d0290184409829018450184408829098450680d0882919045088290880e070450080d088e90080e1c06b0184401845098000680d1609c160350882900845008450680d0880d16020008451609c0084509800048640880d0400d04820018450486b0184501844
|1=>0x80d0182108829088e90080e0698d08829160290218d0000708829048350184502029018460880e0a0bf0680e020291000e0a02401845021ad008460982b088e90080e070460080d0880d020290d02901844089a90680d06846088860982902197018230882b088290000f088290a027018450888401821018450880d08829018290680d02029018450184408865008290486b0202901845018440486b01845
|2=>0x88290880e0182901a7d020460a06b018444b8070209d01829098450680d4a8450a00c49829021af008461600d008451084713835018291502901846020290184503045008350082902195018230080d139af01829018b2008450080e068451384701970160293402906846088e90080e438460a00f0482908a11068290482b0880d020290480701845040b20682919045020290880e018b2020290184606829
|3=>0x68050982b0680d0202906829068450482001845018b20084501821008450680d0880d0c84c0680d022d1138440180308829190350880e018210080d01829008293580d008460682902029000370882908aa73d0450182b08864088050082902197018230682908805088290882b0080d0d029018450184401829018450184702029009a106846098b2018350202900869018441084401821018450882919045
|4=>0x1602b018450d0290184402175088670080d0180008829018454b8070209d0c80f0084e0680d0a024018450880d138470182906979018453282901823068296482b018450a06b02029018440680d0880d01829070350080d0084d0680d0884e0680d098b01609c0182900845019a10684601829088290184501822018290886700829068b200845022ff0000c0882908829048370880d088eb0080e5c82902018
|5=>0x882901829068c90880e0a027018450886501844018450c8470082902143138370182906aff0000c5c829020180201a018450000e08829018452e00f088656e0290206b018440486b01845018440682904807018450482b01845190a9018460880e0982b0215d358290084601829088290880e0000f0882901b65138460182904047068290201a068050884e0680d1b02b018010882901972088651084413835
|6=>0x20290680d06845068e90080e0182306829018290880e040057c8290184501829358290482b0184501845020290201a0083500afd0000c088290212101844070813580d00846068290680d02029021210d0290184401845018447a80d4f829088af0c80f0886700829009a1068460886508829360290882904805018450482b0880d00ad113844018291384401829020290686b0880c00a7d0204606ad313844
|7=>0x68290882b0184516029008451380701829088290680d0183506829018290680d018290080e040050682901821068290184502029020290184400845068290a00f0202901829008460083500829088370082906846068051384601829018290080d008290080d04045068290882906829020bd0680e01820068291384501829190290880e0209d018290c837008290880d008460182902045018290880d0680e
|8=>0xa7f0204604005068290084501845088290880e0680d0202b0209d0182901829020460880501846008290684508829008460686b0880c1002906845018450184501a7d0204613837018290a00c020290202501845070450080d0a047020290680d0202910005068450200208829018450202b088290184504807018450182b0684604807018450886600829360290200e1602b008451d0290080e0184502029
|9=>0x35088290882901829068460080d068460202908829020050182b0680d068690880c020290080d018450680d0880d3d0350182b0886500829018453e00e0882b3d0450182b00829018460d02a018440183500845068b200845020290880e01829068460182900835178450680e1383501829088290080d0201806805358290084600a7d020460d02901844018b2008450882b0080d1384601829190350880e
|10=>0x20290200d00845020050202b06846068050080d020290880e02046018290184502026018450482b018450482b01845021af00846018b100845018290680d068450080d01845008450680504829018450000f088290206b0184404047068290886700829190450880e018460880e1000e06845088e90080e019a3068460d029018440084d0680d0000c088290180706846020690184401845018440201a06805
|11=>0x182b01845018440680e06829
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x984242000000008c40000848000000000000000000000201000000000001d300001b200000000000192058c00005080000000131040c0d3000000002c80000000092000000000000000000000000000002040000188000000000001440000000000000003200000030000000
|5,1=>0x10903f30f0c0000e100000d4c323000030200000000b4c000000000000002b200000000000000000000009d0000000000000000000000000
|6,0=>0x23088b1000089221c8000000084320c481220040001fc47e11f447b200007920000781000075300007321c0c6d31b046a20000000000068219c4652000000018c8000000000018845f300005d217040001688582000057115845421488000000050213c44e113444b20000000120c462
|6,1=>0x38c400000000003884e0237c4dd2368cd733548d32340c00033880003308ca23208c5330c8c2130440002f8cbb3000000000000002e480000000b632d08b222bccad20000ab22a840002a08a620000a332848a0127889c22688000000099125c80002548932000091224048e2
|6,2=>0x4c480004bc80004b840004b092a249cd252000122348080000000000474d1b24648000460515344c910343c400043850d10000000428c000000000041cd06100000004108000000000000010223fccfd200000003e8c0003e08f623d44f233c08ee23b08ea23a44000398c0003908000
|6,3=>0x6308000000189361c9843000182200018025f897c200000005e897915dc80005d497235c096e25b456c100016a25a45672590d61358055e200015c20000000564c0005605553548d502534d4b2524947251854425088000000140200013f14f0d3a24e440004d8d3424cc4000
|6,4=>0x1b616d09b226c080006b89ac26a4da720001a610001a42684d9e367099a26608000000196265080000001931000191264058e20000000
|7,0=>0x8c8a3028b8a2c28a8a28289c6261890a222880a1e2870a1a2860a162850a122840a0e2830a0a2820a062810a0228045ff27f49fb27e49f727d49f327c49ef27b49eb27a49e727949e327849df27749db27649d727549d327449cf27349cb27249c727149c327049bf26f49bb26e49b72
|7,1=>0xabcaad2aacaa92a9caa52a906a22a80a9e2a70a9a2a60a962a50a922a40a8e2a30a8a2a20a862a10a822a00a7e29f0a7a29e0a7629d0a7229c0a6f19b4a6b29a4a681998a642988a602978a5c2968a582958a542948a502938a4c2928a482918a442908a4028f8a3c28e8a3828d8a342
|7,2=>0xacc6b12
|8,0=>0xb106c31b084000b046c01afc6be1af46bc1aec6ba1ae46b81adc6b61ad46b41
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x1490000a28000506000202000100000060000022200010b00008200004080002000000f3000078800038400014000008200004080002000000a6000043000020000005000002600001200000880000400000180000060000018000008000002000000
|1=>0x408800204000100c0008020004008002000000f3e00079b0003890001a7c000d3600061400030900014000009c20004a0000248800120800090000045000021800010680008200004020002000000f7c00073e00039b0001c78000e2c000704000302
|2=>0x10100008048004020002002000bd58005e6c002da60014d10008500004100002002000f9f0007cd8003e4c001e24000f10000769800384c001a0c000b9b0005c1800292800130400098100048b000243000120c00090200044880022080010a6000813
|3=>0x12241008300804173602090601048100820180407060202870100030079acc034d2601a0b300c149806044c0300000160a1008400804042c0117a60083d300414b802045c010226008001002000000a2040049020024200012000008208004102002021
|4=>0x601010228e4c111f16088e8b0442498203e6c101f26080ed30405c98202e0c10072408020a0401040200800100004070c830307498120000085142041fdb020de58104bac081d06040d9102054181022180808060401000200010100000060000024c80
|5=>0x2403cd9201e4c900726424c822123419029acc808d064006872000000923a4c481f22230801118001882fac4415d6620a6b31041e98820b4c41052620091110040188004444000221040860813c584082c4200f361004800801cd84006182001000c0208
|6=>0x14c02d3840001b222a2d91070688024a4040011411a1ca08706501f812801c39322e2c9907964c839b2641459300e5c91cd0648a2832432411218a0c905506482783
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x330202002000020200110000020000000002000000000000340000000000000000002702000005000200000000000006000000160002000000020200020000061012000002000002000000000000000027000800000027000000000200020000
|6,0=>0x150000000a550b0eab21573e39003c000e5c01372e770600163c000000001c00001c02834e0200023a00012d0062023a010e3200000b0100010281cf560116060002010000165f0715002b275f0e00010006000300025195b70200000002270200008e006300a150000160000e0e0006061b0200000e01a430010000370e
|6,1=>0xe0000867e1f00020002460200001c5f02000e1e0258060200165f0233385d02001b00003500278544013c0191025f0e01000002005f3668820016025f0002001c0004000e011a92003331000000035e0200290d027c270027712c00610067001c0b000001000000000259010000c3002802270f08020e02270069000200
|6,2=>0x64923e1b002d02182a005f0002c250021b0c00003b02000006008417020000
|7,0=>0x444b4faacb2f77b2787952b96f53535a224c53a67d489a389b7f7c43c1d3a3539e2dcca5b49453243f4c2fb097421438a809598f9c54af403da59876ac7b5bd04ab565904cbba0a99db8bdc7aed2c0b1c78b7b19496d73c6ad2313c54db36b2ecda26e70ce969965d14174668d896a7280bcbf387a25c975889f45becca73847
|7,1=>0x93ca
|8,0=>0x248c534b38b9c7c8b6d48a87ba6cc4539c26
|9,0=>0x1d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 7 roots_220 ops++addP pm 1 dom_94 7 roots_94 ops++addP pm 2 dom_86 4 roots_86 ops++addP pm 3 dom_198 5 roots_198 ops++addP pm 4 dom_212 5 roots_212 ops++addP pm 5 dom_200 4 roots_200 ops++addP pm 6 dom_196 4 roots_196 ops++addP pm 7 dom_218 7 roots_218 ops++addP pm 8 dom_214 6 roots_214 ops++addP pm 9 dom_206 7 roots_206 ops++addP pm 10 dom_154 5 roots_154 ops++addP pm 11 dom_158 6 roots_158 ops++addP pm 12 dom_138 4 roots_138 ops++addP pm 13 dzo_200_16 4 roots_200 ops++addP pm 14 dom_90 4 roots_90 ops++addP pm 15 dzo_204_16 5 roots_204 ops++addP pm 16 dom_92 4 roots_92 ops++addP pm 17 dom_30 4 roots_30 ops++addP pm 18 dom_142 5 roots_142 ops++addP pm 19 dzo_206_16 6 roots_206 ops++addP pm 20 dom_210 4 roots_210 ops++addP pm 21 dom_156 4 roots_156 ops++addP pm 22 dzo_202_16 5 roots_202 ops++addP pm 23 dom_78 4 roots_78 ops++addP pm 24 dom_204 5 roots_204 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_200_16_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_204_16_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_206_16_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_202_16_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_204 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 7 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,10),(2,34),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(32,33),(32,34),(32,40),(32,96),(32,160),(64,65),(64,72),(64,96),(64,192),(66,67),(66,74),(66,98),(66,194),(128,129),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>3
|5=>71
|6=>160
|7=>87
|8=>20
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x18d2c11c09101b1
|5,0=>0xcee02c740f8fd4a8ea128774a7d1757bc7c70823698936891067fdd623955f0d05c84b577f75000e4f1b84e92f4d01d4c9e749f8648040438bf3b04d370f03471933de431f6830e382ebc32e9492a2ee280bd2529c23bde236192107120f421c0381a3791a2121908b185f91850e167af15b8e15b54159711441712abb1259c111150fb0e0f0750d3fb0c5620c34e0b7e90977f094a608090072a2068fb05680048290351b03387025960184a0161d00112
|6,0=>0x5c3545b8a95af095aa1f59005557945551051fb451eb6516954f9af49a53469ff45790434214213b41b4840beb3dded3c4f33bc873ba6a3b171393723903e38dea38072370443666935b6435a5434ccc3388f3258a319552fc382f2d52d6c52c8282bb5329dab2885227f4b27a942794626eaf26b4522db022af721e1f219f7217982113f1fe441fabf1f42b1e9f81e7b61d6711d23a1be7b1b6ab1b4b51b15c1ac511a4931a3d719508184211782616ac91690e15c4b156511432213ac7135fd11fc3119f01124e10cf8103400f97e0f8e80f5c70dec40d9c80d2070cf840cc870c9350c5590bfc80b7e90b70b0b5dd0b42d0b4240b3a10ac200abfa0a8320a5c4098a108d210760c072a206733066be0642a057a205408053e404849047fa046ae0444c0408a036d302e6b02db702582024fe0221b01fd30156000dfe005a0
|6,1=>0xddf45bcec2b7765b1524abc3a948488b9998774a83fa482a6b7c8cd74e16738f870c7c6ece46eb586e87d6df1c6c9ad6c13a6966d68b7066f8c6602665ccc6530f6512663ffb626d361dba5ec895eb40
|7,0=>0xddf45a16b1962b284b4682708825fa7ef1a70dc06fcce6ccc168390648005d0e95bc1d52d6b4fdb44ef744bbbc4959a4792c462984382d420dd3bdc93a23e3979138de738c9e3842133a50336b733163330ac329a93202e3168e314003086a304a42f8f22ee2f2d2592d1382b7f32a2a729ed0291aa2915a283622717c23a0b2374722e8322c7b21cea1e25a1dae91b3d418d08185fc1688915c4e13e13121a7113360fd140f58c0e3f10e2490de7b0d3e70c7bb0c5ba0b3d208827083e40838407453055be047280443703f0902eb8020a900ffe00e050065a
|8,0=>0xa2b7e77bdf63b5961f5d5de5e5aa7e56565424ee3fd043891e386903033021abc190201439c1342612f3c12e870979903e38
|9,0=>0x7ccdc51d3d0ee3d040d9
|10,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000000000000f0a0000000000000f0af0f00000f0000000f0f00000f0000000a0a00000a0000000a0a00000a00f0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0ac0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f00000f0000000f0f00000f0f00000a0a00000a00f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00f0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
|0,1=>0xf0a0000000000000f0af0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0f00000f0a0000000000000000b0b00000b0b000000000000000000000b0b00000b0af0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f0000000000000000003030000030300000000000000000000030300000300f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000000000000000000000000000000f0f00000f0a00000f0f00000f0af0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f005050000050500000505000005050000050500000505000005050000050030300000303000003030000030300000303000003000000030300000300f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0ae0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00f0000000f0000000f0000000f0000000f0000000a0000000f0000000a
|0,2=>0xf0f00000f0a00000f0f00000f0a00000f0f00000f0a00000f0f00000f0af0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0f00000f0f000003030000030300000f0f00000f0f0000030300000300505000005050000010100000101000005050000050500000101000001001010000010100000101000001010000010100000100000001010000010000000000000000000000000000000000505000005000000050500000500f0f00000f0f00000f0f00000f0f00000505000005000000050500000500f0000000f0000000f0000000f0000000f0f00000f0a00000f0f00000f0af0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000f00f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000030300000303000003030000030300000303000003020000030300000302b0b00000b0b00000b0b00000b0b00000b0b00000b0a00000b0b00000b0af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000000000000000000000000000000f0f00000f0f00000f0f00000f000000000000000000f0f00000f0f000000000000000000000f0f00000f0a
|0,3=>0xf0000000f0000000f0000000f0000000f0000000f000000000000000010100000101000001010000010100000101000001010000010100000100f0f00000f0f00000f0f00000a0a00000f0a00000f0a00000f0a00000a0a30300000303000003030000030300000303000003030000030300000300f0f00000f0c00000f0f00000f0c00000e0e00000e0c00000e0e00000e0cf0000000f0000000f0000000f0000000f0f00000f0f00000f0f00000f00f0f0000000f00000f0f0000000f00000f0f0000000a00000f0f0000000af0f00000f0f00000f0f0000000000000f0000000f0000000f0000000000f0f00000f0f00000f0a00000f0a00000f0f00000f0f00000f0a00000000f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f000000000000000000f0f00000f0f000000000000000000000f0f00000f00f0a00000f0a00000f0a00000f0a00000f0a0000000000000f0a00000000f0e00000f0e00000f0e00000f0e00000f0e00000c0c00000f0e00000c0cf0f00000a0a00000f0f00000a0a00000f0000000a0000000f0000000a00f0f00000f0f00000f0f00000a0a00000f0f00000f0f00000f0000000a0050500000505000005050000050500000505000005000000050500000500
|0,4=>0x500000005000000050000000500000005000000000000000500000000a0f00000a0f00000a0f00000a0f00000a0f00000a0a00000a0f00000a0a0000000000000000f0f00000f0f000000000000000000000f0f00000000f0000000f0000000f0f00000f0f00000f0000000f0000000f0f00000f003000000030000000303000003030000030000000300000003030000030000f0000000f0000000f0000000f0000000f000000000000000f000000000000000000000000000000000000000000000000f0f0000000000000f000000000000000000000000000000000000f0000000f0000000f000000000000000000f000000000000000f000000000000000a000000000000000a00000000000000000000000000000000f0f00000f0000000f0f00000f0000000000f0f0000000000000f0f0000000000000f000000000000000f0000000000f0f0000000000000f0f0000000000000f0f000000000000000000f0000000a0000000f0000000a0000000f0000000a0000000f0000000a00000000000000000000000000000000f0a00000f0a00000f0a00000f0af0f0000000000000f0f0000000000000f0f00000f0a00000f0f00000f0a00000000f0f0000000000000f000000000000000f0f0000000000000f00
|0,5=>0xf0a0000000000000f0a0000000000000f0a0000000000000f0a0000000000000000f0f00000f0f000000000000000000000f0000000f0000000000000000000000000000000000f0f00000f0f00000f0f00000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000000000000f0f00000a0a00000f0f00000a0af0f00000f0000000f0f00000f0000000f0f00000f000000000000000000f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f000000000000000000f0f00000f00000000000000000000000f0f00000f0030300000303000003030000030300000000000000000000030300000300f0500000f0500000f0500000f0500000f0500000f0000000f0500000f0050500000505000005050000050500000505000000000000050500000000f0f0000000000000f0f0000000000000f0f00000f0f00000f0f00000f0000000000505000000000000050500000000000005000000000000000500f0f0000050500000f0f0000050500000f0f0000050000000f0f0000050050500000505000005050000050500000500000005000000050000000500a0a00000f0f00000a0a00000f0f00000a0a00000f0a00000a0a00000f0a
|0,6=>0xf0f0000000000000f0f0000000000000a0a0000000000000a0af0f00000f0f00000f0f00000f0f0000000000000f0a0000000000000f0a00000000000000000000000000000000f0f00000f0f00000f0000000f0000f0000000f0000000f0000000f0000000a0000000a0000000a0000000a
|_,_=>0
def sP:Nat→Nat
|0=>0x1a2048a16ac68914445a91a205040604028129c88d009928a080c009140d20d002048a3a0c02242245040680498144401e122888d0064e091444689147418038245033668c89302888d2e28203020041614101811228a941a00493080c10018488901a008901e340080e182840608080
|1=>0x1a01b0c109c203402438a2201792129c88d38b83941a0040764186b5141818100209b80c0c4b74e18189269c194343041120340362e253840630ba54e101a2122819b00259a70634487621801912283301abd7084e446894e2960d00785111e3400c4e10181002438a563400c249c88b
|2=>0x7048a16ac69912181901a317112034019122888b1a2452d58340094e1818518493911a317072834009142d58d002451578340214a2050406bc6084e4469c124c19434253bb0634e0914b068012291ab1a0040a223c6802e245033601d094e1018012585042a01a89140d68018e4511
|3=>0x230c680402438a0c0c00c105830334357880e2888d00317272234041122888d00944162628303129c3038069792129c3031a30407223402e106138a0c3440914101bf24204a714446891455f0d00245145834019141818f1a79009144402012283030030ba7080c4bd261802f122958d
|4=>0xbd708141858d129c5035a3401e10245111a0048a760c680429448a080c01c1024986066978c129c88d0070409141019a18e45060634009148c18d007848a223401c124c3033518487223402f5c253861634e09141019a121c30b8a35a89141819a00d92881410180124d386071040a
|5=>0x102450336340214a20506063440a0c0c78d007048a06ac680403048a0c0c02510283037e2048a06906805e3040a2234009140cd8d007048a0650d0d102450616c069c18243861635709144480d003049626101808cb85111a00498144478d0024503483400812291831a006170c0c10d
|6=>0x122820300d9088141818d38245062a34036125850406006252c4c30300b840a06506805e203a70c0c68c5c613861a0061214446801824503783401c4a205060668e09142c1941a24504072000c4e1818f1a004a70c0c80d0030406060868038945060668609304458d0088b891410180
|7=>0x14181811a00e094e2888b1a84496141818d12288d01a01b082628203002438a0d386802e204934e181af18213860634b89269c30310245040724017129c504073048a072c6804424503283402e144650d00844a7141818d38d448a0c0cd0914181850024504072402f12281941a01108
|8=>0x1a204934e1018c12281ab1a0048a701819a38245035a340094e2830b60344a70c0c70d6c245037834035122819b1a00e09269c30334317270c2c68c242138606346080e1858d44d448a0c0c00c10181d11a309270c0c6a1124d38606349090e1880d004848a06506804a24503783401c
|9=>0xc0c02f12605111a006270c0ea8d18213840634f2e122888d00704090e446804a4c506060402e682830d0088496141018038243911a01a971228303015040a0c0c680129c504072002ea4283031a012882c2830318b8303203400c2e9c3031ad8e09141018010283031c34c891418583
|10=>0x1a8448a080c01c5c605061a01109140de0d00bc48a0cc06806a24503283400c24b85111a00e09140d20d00790091418180382450616c0689140eb8d00243d60c0c6804a20503283401e38245111a00f1912283031abd0091418180122888b543402f38245111a00487144678d0031296
|11=>0x242438a0c2c6801228350063402512585060601789144468010249a70c0c6a212283031a0048a06b4a0d002538a080c080122888f1a0110a0c0c08d002450328ac68050245111a0100914181803c2438a223401c182451116344a70c0c6da323048a223403642245060668cae122830b
|12=>0x634012122888d017448a080c01c12283036034025109c50606351094e283031a01288262830300317070c34036182450606680094e28303903400c2e205060634025124d3860600487141818f1a012894e2820300d8e09141818d0030b8a0c0c680383128a0c0c680382538a0c2c18d
|13=>0x141818d6a2450606340125c2538a0c0c68c4a9c3031a00496141019a00243a722340081228303c036309261818d011848a080c68012288df1a0060a0c0ea8d0020498141818d1826106063400c129c2031a011092c283031a0040915783031a4840914446801824b06063401e129c506
|14=>0x121c5061a01089141818d0079709141818d0024b1314101802e24b0a0c0c6805c243a70c3401c5c283031a0048a641818d011928a0c0c6805c205061634e08121c3031a0049314181dc1a01a8812283031a01289c22830300704870c0c680383048a0650680383048a220c6801024b27
|15=>0xc0c6804a20504060048a0c0f10d0070609141819a1a24506071c680323048a0c0c680182138606349090e2830d002048a0650680184970a0c0c68012281941a006092c9c3031a0111c12283031a00498144458d005c40914101805e7048a0c0c680121c506073c68012283033e3405b
|16=>0x1260506160c6801228303aa3400812282031a02309141818d00304a70c0c6801228303c63402212283031a00e09140ca0d005c4a7141819a1a24b0a0c0c08d005d2894e283031a2450606a868024245060640680382048a080c6801228303b83401c12282031a00609144458d013048a
|17=>0x121c506063402e12283031a0048a080c680102450606340090e2888d00b848a223402f1824506063401c1024506063401c12283031a00498141818d00304870c0c6801824506160c680124d38606340092c283031a00609141819a1a01b0c12283031a01288141818d002438a0c2c680
|18=>0x48a0c0c680
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x9500540005
|5,0=>0x17f61796173616d61676161615c51575151614b6145613f61396133612e51286122611c61166110610a610460fe60f860f260ec60e660e150db60d650d150cb60c560bf60b960b360ae50a950a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60385032602c60266020601a6014600e6
|5,1=>0x1a761a1619b6195618f618a51855
|6,0=>0x351734a7344633d7336732f73296322731b7314730e6307730072f972f272eb72e472dd72d762d072c972c362bc72b572ae72a772a0729a6293728d6286727f72787271726a7264625d7256724f72487241723b6235622f62296222721c6216620f7208720261fc61f571ee71e771e161db61d471ce61c771c161ba71b461ad7
|6,1=>0x4fd64f674f064ea64e374dc74d574cf64c874c264bb74b474ad74a674a064997493648c7486647f74796472746c6465745e74586451744a7443743d6436743064297423641d6416740f7408740173fa73f373ec73e663df73d873d173ca73c463bd73b763b073a973a3639c7395738f63896382737b7374736d7366735f73587
|6,2=>0x5d675cf75c875c265bb75b475ae65a865a1759a7594658d7586757f75796572756b7564755d7556754f75487541753b6534752d7526751f75187511750a75037
|7,0=>0x7a6879f7798779087888781777a7773776b8764775c8755774e77477740773a6732872a8722871b7714770c870486fc86f576ed86e676df76d966d276cb76c476be66b776b076a976a2769a8693768c7685767d8677667166698662765a8653764d6645863d8635862e7626861f761786107608860085f885f175ea75e465dd7
|7,1=>0x84e7847783f8837882f8828782088188811780a780377fc77f667ef77e787e077d887d267cb77c477bc87b667ae8
|8,0=>0x8df68d968d188c988c278bb78b478ac88a5789e7896888e8887788078788871786a7863785c78557
|9,0=>0x8f978f278ec68e57
|10,0=>0x9006
|_,_=>0
def wAt:=mkWire dB 100 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x381b00354e250029242b14954a0112350c35140100950c351a256a356a1b3837102912010cd10e200029140d0025140d64354eb8120d002914015c29120d0c0d06b62835381b4e252c2714250c0d1625060100a9182f12294e97140146370651381b1029107d0e23140d120110291201125a242b140d12011c35182c000d1425
|1=>0x351425700d4a9c1a2514011a29129d00291a39182c14250029060112295c01120d0c0d0029381b1801122906250c0d00291201180d381b4e2500290c39182c142500290601381b1029120112010c351835002914b95c0106250c0d381b129d14014eb814010629120106254e9412011a2514011a2900296835101c140d1201
|2=>0x254a2912350c353427003514011a290c0d5c2b120106253c37101d00253429003512290c0d121d140d00251229120d0c0d14010c0d13090e03140d26011a2912010035262714011a295c2900b9120d140112290025140d0c0d06254e0d00290c35342b1a01120114010c0d100d12013c375c9d120d0c0d140112690c351401
|3=>0x5c29000d120106252835381b4e2524290c0d100d12011c19182c000d122900da4a2912350c351435102912010c0d180d122900290c3510291a0112018e25182e000d1229381b102912015c9d120d0c0d140100311a0114251a2900320c0d1425062914b9120d0029003100350c3514254e27000d140106294437186900351229
|4=>0x12016c034a291a253c27380d10290025381b102912013c375e01180d1235342b1a0112013c1b380d10290c0d1201180d1229381310290c351201381b10291201380f10290025000d180114250c0d144a5c01120d004d0c3514251a29120d18030c0d12290c0d12624e0d14013c1b12614e0d14010651381b10292e2b10350025
|5=>0x383510291201124d260114350c35123526011a291229381b102912010625121d140d0025120d4e0d00290c0d1425100d0025441b6c011835003510291a250025381b180112294a9f12350c35140130274e0d00293c2b30254e0d0029145e1035002510291a011a2500251629000d0c0d14250c35145d103512016a1b38371029
|6=>0x14010c0d8a0d4e270029262514350c350025073d101f140d12011435103512010025180d122900294a011a2514011a29262314350c354a0112350c350029153510371201381b10291201102b06250c0d002544032c254e3500293837102912011c35182c000d12290c35104e14351201262114350c35120100da18351425440f
|7=>0x291a012835381b10291201380f4e251401163006010029122938371029120114354e2500291a01060106251229002914011229100d00250025060114250629383738351029120112294e0f1401120114011425100d002500da26251435144a100d1201441b4e9500292c274e354e2500290c0d4e2500290601440312594e35
|8=>0x1201125a260114350e20120d140d12012c250c354e351401129d0c0d1401062910353837102912011325104e143500254e9612350c35134d4ebb120d140114691a011a250025242b5c0106254a011425123514010c3518351801122916301201000d12293c03182d000d12290c3500291435002538470c0d180112294a9c1a25
|9=>0x180112293837102912010c0d5c0112290625380d102912013c3712614e0d1401380f10290025b21b016118371229153d101f140d1201381b10291a250025380d1029120100be00bd180d14251801180d0c0d12292601123514251a29121d0e0106290c0d100f1201002912290c351201002912294eb9120d00290c0d140d1029
|10=>0x104f14351201381b102912012c270c354e35140130274e0d0c0d14014427145d10351201381b10291201b6290c0d5c03120d3c3712614e0d140112610e01140d0031000d0c0d14251868142500291a015e03180d0c0d122900da183514255e0314b906250c3500da1835142506254e0d4e250029441b12594e351401380f180d
|11=>0x12010c354a031235380f102912010025123500292c254e35002900251a251435120d142506291a01183512294e9612351229103500251a2514011a2912620e01140d12350c35140118011835122914251035002518011a2514254e2500290601122d0601140d8a0d4e27002912354e3514010c0d180d1425002514011a292771
|12=>0x180112290c0d1801122900254e35002938371029120100b9120d14011a251229002934291a010c350c0d14010629162b06011201180314251a2918030c3512290e27140d0c0d100f0025142512014e0d14010e031425062900290c35122912594e3514014e3714011201100d0c0d1201260114251a29380d4e251401100d0c0d
|13=>0x291229383510291201162906010c0d0c3510351201180d18011229101f1201101e140d1201140d5c03120d00da183514254eb9120d0029260114350c35126934290035140d120d14011029062500254eb8120d0029123518031229060106250025140d10291201104f1201383710291201004e1a251435180114250629381b
|14=>0x381b1029120134251a011401125a4e351401009512351401182f000d1229144a100d120110290c351201104f1435120110290c3512011229000d0c0d1535103712011a250c350025017d0e27140d180100351229182e000d12295e03180d1229120100291229122d0601140d381b102912015c0112290625381b102912014e35
|15=>0x140d06250c351201140d0c0d06250c0d180d122910291201102912014e0d140114250629000d1229140114354e35140100351229183512291a2500250601140d1629000d100f12010c35120118031229002912291627000d12594e351401
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x18000
|5,0=>0x772000000000000001c946d51a50000000000019506231754000168c000000000000000000000564000052413cc4a5000045510143c40ec43740cd02e50a542450000204071000006c400005d0000050c000000012200000e4000000002900000000082000000001c40000000061
|5,1=>0x20d40001f94795
|6,0=>0x5b8d6b359d164358115d3565156354914f352d147450d13f44f0d3844d4d3234b912b349d1234480d1d3468d16444910e4429106440cd0033f10f933d50f143b50ea33990e243790db335d0d3433d0cc33210c443010bc42e10b442c4cae32a90a6428909f326d097424d09032310884
|6,1=>0x94924e4929246490ce3f48f0e3848d123048b12284894e21487521a3859212483920a481920247f91fa47dcdf340001f037b11e847911e047711d847511d13738c00072cdc7470d1bf46ed1b746cd1b036b11a84694da14678d9b365d1934640d8c4621000061118135f517945d51714
|6,2=>0xaf52ba3ad92b24ab92ab3a9d2a34a80e9c4a612944a44e8e3a292864a0927e49ece7749d0e7049b4e6949952614978e5a400000009590000
|7,0=>0xdecf783dd4f723dc0b6d3da8f673d90f613d78f5b3d60f553d48f4f3d30f4a2d1cf443d04f3e3cecf383cd4f323cbcf2c3ca4f263c8cf203c74f1a3c5cf143c44f0e3c2cf083c14f023bfcefc3be4ef63bccef03bb4eea3ba0ae53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13
|7,1=>0x3c03ef4fba3edcfb43ec4fae3eacfa83e94fa23e7cf9c3e64f963e4cf903e34f8a3e1cf843e04f7e3
|8,0=>0xfa4be72f94be32f84bdf2f74bdb2f64bd72f54bd32f44bcf2f34bcb2f24bc72f14bc32
|9,0=>0xfb87ed1fb07eb1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x18000040c0010200040400100400400000c000024f00091400244000900002300008b000208000810001000003240004c00012c00044000104000400000f00002000005000009000020000050000100000300000400000
|1=>0x802001e5d00793401a6c00697401a5c0069300180000501001000003d3400e4d00393000e3d00303000c0100300000a4c0025240090500212000841002100008290020740081500202400805002004008000018d000605
|2=>0x33c340ce4d032c300c90402bc340ae4d02b83008f4d023c3008e4d02383408e0c022c30088410201100804002000006e4d01803006008013934043440104100400400b93402b4d00a0240234c008d10023000088000210c
|3=>0x2408b09002c2400208ae4d21b93486a4d2109308400820ad3482b0d20802081a2c2039b480e4d2038f480e1d202d14808412001004020908000011e6d04687011a0c043874108140410b0102280400a0100080400000ee4d
|4=>0x6029358040d60010110e4d44382510e0542a83108b0c422c1104e4d41293502f4d40b93502a4d408d3102308408c110220040793500e7d40393500e2d40387500634400841002002439b490e2d2428a49082d2418a09042c
|5=>0x842076106148410721021c8400120cf4d82a83204f4d812d3604945810d120430c8105320414481043202a4d80a92601e5d80793600e5d80393600e3d8001020001480001188a486200318490160793580e4d60387580e0d
|6=>0x388244e079378140ce0393780c09e0301780a4de0193780605e018138040de008178004de0013380041c1a00700a4da2081288008a0703281004a038b680e1da030b680400a0010231e5d84387610c15
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x200
|5,0=>0x1b00666c004f000000000d5c0c000000401a2b00220000000000000900110a2d00270f1c101107232b6c00190300080048004f00006b0005000023000036000061000010
|6,0=>0x8312af3d23a5624625a60106030b82a7c037cc0b740c671ba99f0001d2a4b3cd236fb68649000501ca0156140bbb91bf05690138b904c4183c00288701127f158e755d03d20a3a3f0407d74c241d860650039a058f331a6d9d4864974d2a05a89103452e13c490c8042955d89942c9761b219b530a7d42985963c516997868b1
|6,1=>0x232f6554010a570b23cba0431441390e2301014a011bc3310b1f520100005100
|7,0=>0x34d5bd7ebc8bb2daabdb5eabae47d34b44d9b7d5b534813060c2170a4746346e6a1e77d63589b8cf039e32d6d1dc8034b5a16a7c958a8d5ab07a92a32570ba842c5f3bcec626aa948803be71793e20c1d4d0b472845bc7
|8,0=>0x5a5894d5d97b939673859c8cac4e7babad8ba24b
|9,0=>0x47353dab
|10,0=>0x34
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 9 roots_233 ops++addP pm 1 dom_42 4 roots_42 ops++addP pm 2 dom_227 8 roots_227 ops++addP pm 3 dom_203 8 roots_203 ops++addP pm 4 dom_139 5 roots_139 ops++addP pm 5 dom_163 5 roots_163 ops++addP pm 6 dom_234 8 roots_234 ops++addP pm 7 dom_162 4 roots_162 ops++addP pm 8 dom_202 5 roots_202 ops++addP pm 9 dom_107 8 roots_107 ops++addP pm 10 dom_171 8 roots_171 ops++addP pm 11 dom_170 7 roots_170 ops++addP pm 12 dom_169 7 roots_169 ops++addP pm 13 dom_226 5 roots_226 ops++addP pm 14 dom_106 5 roots_106 ops++addP pm 15 dom_232 7 roots_232 ops++addP pm 16 dom_43 5 roots_43 ops++addP pm 17 dom_201 7 roots_201 ops++addP pm 18 dom_138 4 roots_138 ops++addP pm 19 dom_99 5 roots_99 ops++addP pm 20 dom_195 5 roots_195 ops++addP pm 21 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 9 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffff00000000ffffffff00000000,96),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 71 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 71 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 160 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 87 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 87 0 = true)
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
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,64,68)] (by decide +kernel) lowS_233
def dzo_234_4:=0x505000005050000050500000505000005050000050500000505000005050
def gzo_234_4:=0x505000005050000050500000505000005050000050500000504000004000
def gsh_234_4:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_4_42:Lower true dzo_234_4 roots_234 gzo_234_4 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_4) [(dom_234,4)] (by decide +kernel) (lower_slice_b (T:=gsh_234_4) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_238
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,68),(4,132),(6,14),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,44),(12,76),(12,140),(32,34),(32,40),(32,96),(32,160),(36,38),(36,44),(36,100),(36,164),(64,68),(64,72),(64,96),(64,192),(66,70),(66,74),(66,98),(66,194),(128,130),(128,132),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_238.map (·&&&dom_238)
def gM:=goal_238&&&dom_238
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x5c24e18c19
|6,0=>0xcbec6c32fc75e1972d5d61b562ee22188490ede6
|7,0=>0xc209395ed0927808d9286604c64c120ffab0ff9f01a8b
|8,0=>0x6910868b393787b
|9,0=>0x1305b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa000000000000aaaa000000000000aa00000000000000aa01555400015554000155540001555400015554000154000001555400015402aaa8000282800002aaa8000282800002aaa8000282800002aaa80002828000000005550000000000000555000000000000055500000000000005550aaaa0000aa000000aaaa0000aa000000aaaa0000aa000000aaaa0000aa01414000014140000141400001414000014140000141400001414000014142a8000002a8000002a8000002a8000002a8000002a8000002a8000002a80555500005550000055550000555000005555000055500000555500005550aaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa00000001111000011110000111100001111000011110000111100001111000011112aaa8000000000002aaa8000000000002aaa8000000000002aaa80000000555000005550000055500000555000005550000055500000555000005550aaaa0000aaaa0000aaaa0000aaaa0000aa000000aa000000aa000000aa00444400004444000044440000444400004444000044000000444400004402aaa80002aaa800000000000000000002aaa80002aaa8000000000000000555500005555000055550000555500000000000000000000000000000000
|0,1=>0x5500000050000000550000005000000055000000500000005500000050
|_,_=>0
def sP:Nat→Nat
|0=>0x2a4c101ca34a8c159d2a3040549a01034a349820714695182069d26080a9519e1038a95182041526080a34a84102ce3518254a841038a950820734e9304083a4c10146660407290660a0e3304a418820
|1=>0x54a8c101469518205952a3040d
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3773162b62471d71761160b6
|7,0=>0x7476d76766075885264b74473e6
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 239 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4812a52a92814814952816a72a92a948128d4812a928128e48128d4815a92a571b28d48149528171b28d48128d4812a949d2812815a94952174a94814814a92814812815a9495
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x6095348d0234ca31cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xe73f29f1c37afa73b29d1027af357939c94e4a21fb8efc56e1bf040007c002000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x1b901690a7
|7,0=>0xf92d9182a66
|8,0=>0x29cb
|9,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 8 roots_236 ops++addP pm 1 dom_174 8 roots_174 ops++addP pm 2 dom_110 7 roots_110 ops++addP pm 3 dom_202 5 roots_202 ops++addP pm 4 dom_226 5 roots_226 ops++addP pm 5 dom_206 7 roots_206 ops++addP pm 6 dom_102 4 roots_102 ops++addP pm 7 dom_230 7 roots_230 ops++addP pm 8 dzo_106_4 5 roots_106 ops++addP pm 9 dzo_234_4 6 roots_234 ops++addP pm 10 dom_234 8 roots_234 ops++addP pm 11 dom_198 5 roots_198 ops++addP pm 12 dom_78 4 roots_78 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_238 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_106_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_234_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_78 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 8 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_238 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_238==dom_238)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_238 gM v ys):RunD true dom_238 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_238 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_238 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030000,1,17)] (by decide +kernel) lowS_233
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000504000005050000050400000504000004040000
def gsh_234_16:=0x50500000505000005050000050400000505000005040000050400000404
theorem lowS_zo_234_16_232:Lower true dzo_234_16 roots_234 gzo_234_16 8:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x40400000404000004040000040400000404000004040000040400000404,0,2)] (by decide +kernel) lowS_232)
namespace S_250
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,34),(2,130),(8,10),(8,40),(8,72),(8,136),(16,18),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(48,50),(48,56),(48,112),(48,176),(64,72),(64,96),(64,192),(66,74),(66,82),(66,98),(66,194),(80,82),(80,88),(80,112),(80,208),(128,130),(128,136),(128,160),(128,192),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|6=>4
|7=>4
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xcb6d634c6f2ca940bb8e
|7,0=>0x8df235f07d1ab2515a8e
|8,0=>0x19912
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a000a000a0a0a0a0a000a0141414141400140014141414140014001414141414001400141414141400140282828282828282828282828282828282828282800000000282828280000000505050505050505050505050505050505050505050005000505050505000500a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a000000000000000000000000000000014141414141414140000000000000000141414141400140282828280000000028282828000000002828282800000000282828280000000505000005050000050500000505000005050000050500000505000005050000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a000a000a000a000a0140014001400140014001400140014001400140014001400140014001400140202020202020202020202020202020202020202020202020202020202020202505050505050505050505050505050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x542170954217085421708a542170b542170a5431708654210a943176542106543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x26e3583b007
|7,0=>0x60ea210b9a7
|8,0=>0x377
|9,0=>0x3e6
|_,_=>0
def wAt:=mkWire dB 12 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14192541a0549a0d490254987e49505410254987e495061f35409
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4998c6603
|7,0=>0x91409c4c2
|8,0=>0x141
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0xfffd7bfd7f3fc7f0540d01c00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x3421
|7,0=>0x9857
|8,0=>6
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 8 roots_234 ops++addP pm 1 dom_242 7 roots_242 ops++addP pm 2 dzo_234_16 8 roots_234 ops++addP pm 3 dom_232 7 roots_232 ops++addP pm 4 dom_186 8 roots_186 ops++addP pm 5 dom_218 7 roots_218 ops++addP pm 6 dom_122 7 roots_122 ops++addP pm 7 dom_210 4 roots_210 ops++addP pm 8 dom_90 4 roots_90 ops++addP pm 9 dom_114 4 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_234_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 8 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_236_16:=0x1111000011110000111100001111000011110000111100001111000011110000
def gzo_236_16:=0x1111000011110000111100001110000011110000111000001110000010100000
def gsh_236_16:=0x111100001111000011110000111000001111000011100000111000001010
theorem lowS_zo_236_16_232:Lower true dzo_236_16 roots_236 gzo_236_16 8:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_16) [(dom_236,16)] (by decide +kernel) (lower_slice_b (T:=gsh_236_16) [(0x101000001010000010100000101000001010000010100000101000001010,0,4)] (by decide +kernel) lowS_232)
namespace S_252
def pG:List (Nat×Nat):=[(4,20),(4,68),(4,132),(8,40),(8,72),(8,136),(12,28),(12,44),(12,76),(12,140),(16,20),(24,28),(24,56),(24,88),(24,152),(32,40),(32,96),(32,160),(36,44),(36,52),(36,100),(36,164),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,96),(64,192),(80,84),(80,88),(80,112),(80,208),(128,132),(128,136),(128,160),(128,192),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_252.map (·&&&dom_252)
def gM:=goal_252&&&dom_252
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9129940ce82645d
|5,0=>0xb339cb234d61be9565fb4565d348602fd2e2dfb42974b24c65234d60cc240cbc80bac604d01
|6,0=>0xebfcbdf329d1436bbc7eb234d7f2d87c4627420f6c1fe6800c656df6449362a235a2764e0364c48e3b2bb388c13582c34d27316072cc4a2686720edb171f7127220e6d10d8c60c4ab095b908eaf08b1606e7502ac20184e
|7,0=>0xb75b6a483b957da84dd6828f07ca3c7a2f8656ad519dd2c120214c31d8b80ed230b5d30a134
|8,0=>0x277841ed7f18815
|9,0=>0xbd29c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x8888888888888888888888888888888888008800880088008800880088008804444444444444444000000000000000044444444444444440000000000000002222222222222222222222222222222222222222222222222200220022002201111111111111111111111111111111111111111110011001111111111001100888888888888888888888888000000008888888888888888888888880000000444444444444444444444444444444440000000000000000000000000000000222222222222222222222222222222222222222200000000222222220000000111111111111111111001100110011001111111111111111110011001100110088888888000000008888888800000000888888880000000088888888000000044444444444444444444444440404040444044404440444044404440404040422002200220022002200220022002200220022002200220022002200220022011111111110011001111111111001100111111111100110011111111110011008888000088880000888800008888000088880000888800008888000088880004444444444444444444444440000000044004400440044004400440000000002020202020202020202020202020202020202020202020202020202020202021111111111111111111111111111111111111111111111110000000000000000
|0,1=>0x888888880000000088008804444444400000000444444440000000044444444000000004400440000000002200220022002200220022002200220022222222222222222222222222002200000000011111111000000001111111100000000111111110000000011001100000000008888888800000000880088000000000088888888000000008800880000000004444444400000000444444440000000044004400000000004400440000000000000000022222222222222220000000000000000220022002200220111111111111111100110011001100111111111111111111001100110000000000880088008800880088008800880088008800880088008800000000000000000440044004400440044004400440044004400440044004400440044000000000220022002200220022002200220022002200220000000000220022000000011001100110011001100110011001100110011001100110011001100000000000000000088888888000000008888888800000000888888880000000000000004444444444444444444444444444444444444444444444444444444400000002222222222222222220022002200220022222222000000002200220000000000000000000000000111111111111111100000000000000001111111100000000
|0,2=>0x11111111111111111111111111111111111111111111111111111111110011000000000000000000888888888888888800000000000000008888888888008800000000000440044000000000044004400000000004400440000000000000002200220022222222220022002222222222002200222222222200220022002201111111111111111111111111100110011111111111111111111111111001100
|_,_=>0
def sP:Nat→Nat
|0=>0x38a1070cd04e2870c505838a1c32013972870c614e2870c158e28b0c50550035013932870c83c14c90c50813840d104e28b24320f04c1c32010044833c13842432010070c54410044033c138b24334504c2c32012890c80811c31850040c2040
|1=>0x3c100e2c90c81412870e114138a8090c504e2870c505f38a10b0cf04e28320578138a7470c504e28440314138a24314100e4c70c505c38a1c350100e28b1c33c50401c31416c02870c158038a1c320168e2870cd04e5ca2470c56413921c3501
|2=>0x2870c504e5ca48b1c314138a8070c814138a10b0c504e2921c314138a9070c504e2870c83c10231c314138a1c350138a1c305638a1c315104e2a01c314100a4870cf14138334505c38a10b0c804a1c320505328320505c38a1c31413a22841c3
|3=>0x1c314138a1c320504e2841c314138a1c314100e28b1c320504a8070c504e2870c564138a2c70cf14138a1c33c50403870c50403972841c314100e2921c314100e2870c83c138a1c314168e
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de9ad467a034e9a66f2c792bc79e30d117853c0ddf8ef57773b9ddc0ed97693b2dd88ebd75b3abdd50ea174d3a4dd18e8573f39ddce0e697
|7,0=>0x709f76fb47d64695f3b1958c6c619efef787b845a22c2f5a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 37 253 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1ce482914e453914747391c08a39347c8291d7850238a4e291c08e2914b4739347082924ec7291c08a39485070138a472214e52171c04e291cf8529157450238a4f3b14a450138a45261ca4d1720a45392cf073914a49201ca45391cf45292ca473928e49201ca45391404a392454729
|1=>0x5391c54e291ce45391c845393cec5291ce452928e45291408e2938a47151c04e2914a45391cf85291408e292ca47391c8453914747392ca473914e4a3914a4c3b1cf45294850b291ce52172ca4739248072914e44391c54b29
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x798c30002884107108600011002
|6,0=>0x279cc392718e19c127e4f49d1b826c4ccd90800604b88000005840015128200094c00232406788d99920005c8a9123
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x5ff5cf51c4df3eb3012ef2eb1ef1090ff0ef0eb0df0c907f06b04904704304104002e02402202001000c008004002000
|1=>0xcefc47c24
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2040010c51c0081
|6,0=>0x4ca44b5060c24830ce1400c60000c00c800d006301682002056
|7,0=>0x1e7d92583d085b65481d722
|8,0=>0x17554
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 8 roots_236 ops++addP pm 1 dom_188 7 roots_188 ops++addP pm 2 dom_220 7 roots_220 ops++addP pm 3 dom_244 7 roots_244 ops++addP pm 4 dom_212 5 roots_212 ops++addP pm 5 dom_124 7 roots_124 ops++addP pm 6 dzo_236_16 8 roots_236 ops++addP pm 7 dom_232 7 roots_232 ops++addP pm 8 dom_180 4 roots_180 ops++addP pm 9 dom_116 4 roots_116 ops++addP pm 10 dom_156 4 roots_156 ops++addP pm 11 dom_92 4 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_252 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_236_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 8 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_252 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_252==dom_252)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_252 gM v ys):RunD true dom_252 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_252 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_252 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_252 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_252 roots_252 goal_252 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_252
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=S_252.noCircuit
def isoMvS_119:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_95
def isoMvS_183:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 7:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_159
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_125
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 7:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_159
def isoMvS_221:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_123
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_123
def isoMvS_246:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_222
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000e000
def gsh_43_4:=0xf0e00000e00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0e000
def gsh_59_4:=0xf0f0f0e0f0f0e00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000fffe0000fffe0000fefe0000
def gsh_111_16:=0xffff0000fffe0000fffe0000fefe
theorem lowS_zo_111_16_104:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_104)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333200003332000032320000
def gsh_109_16:=0x3333000033320000333200003232
theorem lowS_zo_109_16_104:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x2222000022220000222200002222,0,1),(0x3030000030300000303000003030,0,4)] (by decide +kernel) lowS_104)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0e000
def gsh_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0e00
theorem lowS_zo_123_4_43:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0e00000f0e00000e0e0000
def gsh_107_16:=0xf0f00000f0e00000f0e00000e0e
theorem lowS_zo_107_16_104:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xc0c00000c0c00000c0c00000c0c,0,2)] (by decide +kernel) lowS_104)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000e000
def gsh_107_4:=0xf0f00000f0f00000f0e00000e00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,96),(66,67),(66,70),(66,74),(66,82),(66,98),(80,81),(80,82),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>1
|6=>53
|7=>274
|8=>345
|9=>85
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x5ecfb
|6,0=>0xf62f1f2243ef7f2ee76de792ce14a9dedd1cee61c81b2c30e1be9e5bd2a1a8e54a02de9db3e970298ff888dd8287ab66ef6c677dc63a0d60c4756aa1556c354f665457c46fce43f2941b7c3dae2392353614e3383f2f4842d3261fb3e19bfd1414212be110d8c107420f3510f11d0d5dc0c3af0b32509e29091cc06db90417502d0502bc7
|7,0=>0x56b55565d5556c35465453c87539ca537f6524135121550f8a5006d4feb14f1634df604da4a4cc2b4b1f24ace84aa824aa3a481f0481ca469f045aa344dde444e14076c407243f91c3ec003e1a43dffc3d5ff3cc723bfd13bc1d3b3513b0623a98639afb3962438e1937ed8375ea3748936d1b369a93608935f7b354ec34b5033b02332643242d30e4e2faff2f76a2f1ef2ec2d2deff2cd012c1102bebd2b3472b0fc27e67276ab251242408122cd821bc921a98214142102420d3a1fd1f1fb651f5631d7651c5b21c4191c1f51c1131b3cd1a9cf19c5f19c13196f21949818f9c181ae1612d15c15136861348512d12121cb1114d0fc350f77d0ec0f0e6900e5b10dca40d9f90d8ad0cc2c0c34a0c21e0c0e10b5c10925e0882e07b8c0660e05bed05852052bf042af0413d038b502f2101ef201d070182e0162b0030a000ce
|7,1=>0xd84c5d5b36d51a5d4351d42a0d3c52d1cb1d0ba9cb6a9cb0f7c8bdac5e6cc590ac40e8c4007c2437bf2e0bee54be9e5be4bdbe32fbd2a1bd1ecbbdbdbb1b8ba00fb94dab89ffb4597b423fb2df1b2734b2507b2022b1aa1b112fb01eab00bfafc7aae8a6adb67ad2f0ac891ac240a971aa661fa2f53a27779fd2b9fab29ed17976d1970299685495e299573293bdb928389227e91b7c914ca8e8ab8e7aa8df0d8d9748ad9a8a50c891218891e888e08773f872fa859668365583516834c7829c882779824ab80b0680a7f803eb7fdd37de0d7dbbf7d9587b10577643773417654473474733b37195c6fe9e6db596cdb26cb7d6c17b6b25b6a4d268bd768b9266c0c66be36689d64209633946338860a9f609036071c5fef75fe095f3685f1085ea8e5e9815e3bb5dc9b5d8195bfe85b8375b26c5adfc5950f582de5817d57b07
|7,2=>0xffcc6fd3ebfd1c7fa3d9f4029f2783f0f6ded87eeb03bea0e2e9696ded2edece4ddb19dbef6da9a2d95fbd95ed
|8,0=>0x49f34477d4474d746cea468844549644fb0410f640ee43efe43ec2d3e8253e0a13e0633d5ff3cd793cbd7395ed394e238e19382fc37d4f3740a35f7b3511b34e9c3421c339af32d273265231ee531e16315c630f1930ea1309c1305482ff392ec2d2eaa42e91a2e22f2e02c2deff2dba92a9002a20429f9629767289622854f256cc254de252d124cd623ece22c132274f223bd21c5c21414204801f1f91f1731df7b1dcd31c5da1c0281c00f1bb411b43f1b1631b0f91a8f41a59d1a50e197fc1949818ff918dfc1836d173e716c9e16a7216a571636d15d6a14fea14fb6137e312ec71281912563118ed0fc350f41c0f3660f2580f0c40e1970e17d0da060d9bc0ccf90c42e0a80b0996e0928f0910708700084d807f29076cc073aa066c50611805d7504d7304b79040a9038b50353d031ce02b33027c70128000e28002ae
|8,1=>0x9b7609b4139861a98524983f697bb69743896c10962d49606895dbb9527694eb9942799395f936a992ba49284991bbf906eb904208fff28ecf48d6678c3d88c35b8b62d89213891e488e8e88d6a85966852d8843ef83b428384b836068251d815fc80b067faad7f90a7f38a7eb427e8357e40f7dcd77d56f7d5537d0277c27d7bafa79c4177e9876d1b76bc67652a7644f7635c746a17195c70a70705f5700846fc9a6fc916f7716f2366dee16d9f16c17b6b0d86a34c6a3166a14b695ff68b686876d680186763f66d586620e65ec064c956410f6401b63c4e639876384662d3a625f8625f46250460864602615fb7d5e3bb5dbfb5a81b5a6435a6315934258e925743e56e315664f560fa54111540fd538a8537f6536a152b28528905120a508e6508d54fc794f50f4f1574e41c4deb44de764de5f4ceea4ad3d4a4d44a093
|8,2=>0xfe015fdbeffa09df9f96f98eef92ccf69e3f51fcf3a02f1995f11dcf0786f0731ed17eea9a3e9156e65bce4f21e43d0e3f24e3094e2295e1270de234ddfc2dd038dc480da7f7da755d808dd75ded7228d6922d4e28d1340cf08acee89ced7ecc039cb234ca653c98a9c7f0bc7a7ac7a44c6a8cc6732c5c4ec571cc49aec48dec4833c4486c35eec1d3cc183dc13f8c05a5bdd11bce6fbbae9b8972b7d5fb4b6cb455fb2507b1e77b1b2ab0fd6b0f24b0256affbeaec5eacb06ac240ab062aafd2aa618a9331a76efa20fba132fa08e79f5f19e6269ddb29c02e9ba369b791
|9,0=>0xeaa72de234da8e5d6882d047bcec71c865cc4eb3c2985ba0a2b273db0c01b0480afc7da8a85a7f38a7e31a4217a3af5a36fa9ebad9ad2d9850097398957a29539190c1a8dc81869c28418680b06806ca7fcba7f8697e2477cc36776fa6d9546c5396ba506a3f767fee6778561f9f58db65808a5680a466984426d42e874147f3e9633d5ff3d36c3b2ce3a9023a67938013373a7348ea33bb7323e42d77a2929425d8a22f9c2258c21ae921543204a6200b31bda51adc01a4a018776156f113ef1128ab0fb770f0720ea430c8070b3ce09697093d0
|10,0=>0xf90dce6b3fd9c798d3bf83c7d71543581865456c5254f2fbbe20b1905c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffccffccffccffccffccffccffccffccffffffffffffffff0000000000000000ffffffffff00ff00ffffffffff00ff00ffccffccffccffccffccffcc00000000ffffffffffffffffcccccccccccccccc000000000f0f0f0fffffffffff00ff00ffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffaaffaaaaaaaaaaaaaaaaaa33333333333333003333333333333300
|0,1=>0x333333333333333333003300330033000000000000ff00ffffffff00ffffff00ffffffffffffffffffff0000ffff0000ffffffffff00ff000000000000000000ffffffffffffffffffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffccffccccccccccccccccccfffffffff0f0f0f0fffffffff0f0f0f0ffffffffffffffffffffffffff00ff00fffffffffff0fff0ff00ff00ff00ff000000000000ff00000000ffff00ffff000f0f0f0f0f000f000f0f0f0f0f000f00ffff0f0fffff0f00ffff0f0fffff0f00fffffffffff0fff00000000000000000fffffffffff0fff0fffffffffff0fff0fffffffffffafffaaaaaaaaaaaaaaaaa
|0,2=>0xffffffffffffff00ffff0000ffff00000000000000000000ffffffffff00ff0000000000ffffffff00000000ffffff00333333333333333333333333000000000000ffff0000ff000000ffff0000ff00f0f0fffff0f0fff0f0f0fffff0f0fff0ffffffffffffffffffffffffffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000003300330000000000330033ff00ff000000000000000000ffffffffffffff0000ff00ff00ff00ff00ff00ff00ff000000000000ffffffff00000000ff00ff00ffffffffccccccccffffffffcccccccc00000000000000003333333333003300000000000000ffff00ff000000ffff00ffffffffffffffffffccffccffccffcc
|0,3=>0xffffffffffffffff33333333330033000f0f0f0f0f0f0f0f0f0f00000f0f0000000000000000000000ff00ff00ff0000ffffffffffff0000ffffffffffff000000000000ffffffff00ff00ffffffff00000f000f000f000f00000000ff00ff000000ffff0000ffff0000ffff0000ff000000000000ff00ff0000000000ff00000000000000ff00ffffffffffffffff00333333333333333333333333333333000000000000000000ffffffffffccffcc3333333333333333333333333300330000000000000f000fffffffff00000000ffffffff000f000fffffffffff00ff00fffffffff0f0f0f00000000000000000fffffffffafafafaaaaaaaaaaaaaaaaa
|0,4=>0x330033003300330033003300000000ff33ff33ff33ff33ff33ff33ff00ff00ff00ffffff00ffffff00ff00ff00ff000f0f00000f0f0f0f0f0f00000f0f0f00ffffffff33333333ffffffff33003300000000000033000033333333333333000000000000ff0000ffffffffffffff00fffffffffff0fff0f0f0f0f0f0f0f0f0ffffffffffffff000000000000000000ffffffffffffff00ffffffff00000000555555555555555555555555555555003333000033330000333333333333330000ff00ff00ff00ff00ff00ff0000000000000000000000ffffffffffff00ff00fffffffffff0fff0ffffffff00000000ccccccccccccccccffffffffffccffcc
|0,5=>0xffffffffffffffffffffff00ffffff000000ffff0000ffff0000ffff00000000ffff00ffffff00ffffff00ffffff00000f0f000f0f0f000f0f0f000f0f0f0000fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff000000000ffffffffffccffccffffffffffccffcc33333333333333330000000000000000cccccccccc00cc00ffffffffff00ff00ffffffffffffffffffffffffcccccccc0000000000000000ff00ffffff00ff000f0f0f0f0f000f000000000000000000ffff0f0fffff0f00ffff0000ffff00000000ffff0000ff000000000000000000aaaaffffaaaaffaaaaaaaaaaaaaaaaaa0000000000ff00ffffffffff00000000
|0,6=>0xff00ff00ff00ff00ff00ff00f000f0f0fff0fff0fff0fff0fff0fff0f0f0f0cfcfcfcfcfcccfccccccccccccccccccffffffff00ff00ffffffffff00ff000000000000000000ff0000000000000000ffffffffff00ffffffffffffff00ff00ffffff00ffffff00ffffff00ffffff00afafafafafaaafaaaaaaaaaaaaaaaaaafffffffff0f0f0f0ff00ff00f000f000ff00ff00ff0fff0fff00ff0000000000ffff0000ffff0000ffffffffffffff00ffff0000ffff00ffffff0000ffff00000000000000ff00ff00000000000000000f0f00000f0f000f0f0f00000f0f0000000000000000000000ff00ff00cc00ccff00ff00ff00ff00ffffffffffccffcc
|0,7=>0xf0f0fffff0f0fff0f0f0f0f0f0f0f0f00000000000ff00ffff00ff00ff00ff00ffffffffffffffff00ff00ff00cc00ccffffffffffffffff00ff00ff00ff0000f0f0f0f0f0f0f0f0f0f0fffff0f0fff0fff0fff0fff0fff0000000000000000000000000000000000000ffff0000ff00ccccccccccccccffccccccccccccccccffffffffccccccccff00ff00cc00cc00ffffffff0f0f0f0fffffffff0f000f000f0f0f0f0f0f0f0f0f000f000f000f0000ff00ff000f000f00ff00ff000000000f0f0f0f0f0f0f0f0f0f0f000f0f0f00ffff0000ffff00ff0000000000000000ffffffffffff00ffffffffff00000000fffffffffffffffffffffffff0f0f0f0
|0,8=>0xffff0000ffffffffffffff00ff00f0f0f0f0f0fff0ff0000000000000000fff0fff0ffffffffff00ff00ff00ff00fffffffffffcfffccccccccccccccccc0000000000ff00ffffffffffff00ff00ffffffffffffffffffffffffffccffccffffffffff00ff00f0f0f0f0f000f000fffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffffff0fff0fff0fff0ffffffffffffff00ff00ff00ff00ff000000000000000000ffffffff3300330000000000333333330000000033003300ccccccccffffffffccccccccffccffccff33ff33ff33ff33ff00ff00ff00ff000000000000000000ffccffccffccffccffffffffffff0000ff00ff00ff000000
|0,9=>0xf000f0000000000000000ff00ff00ff0fff0fff00ff00ff00ff00ffff0000ffffffffffff0000ffffff00000000000000000000000000ffffff00ffffffffffffffff00000000ffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00333333333300330033333333330033000000ffff0000ffff0000000000000000ff00ff00ff00ffffff00ff00ff00ff00fffafffafffafffaaaaaaaaaaaaaaaaaff00ff00ff00ffff000000000000000000ff00ff00ff000000ff00ff00ff0000ffccffccffccffffcccccccccccccccc000000000000000000ff00ff00f000f0ffffffffffffffff00ff00ff00f000f0ffffffffffffffff0000ffff0000ff00
|0,10=>0xff00ff00ffffffffff00ff00fff0fff0ccccffffccccffccccccccccccccccccff00ffffff00ffffff00ffffff00ff00ffffffff0000ffffffffffff0000ff000000000000000000ffffff00ffffff00000000000f0f0f0fffffffff00000000fffffffffffffffffffffffffff0fff00000ffff00ffffff0000ffff0000ff00ffffffffff00ff00ffff0000ff0000000000000000000000ffffffffffff0000ff00ff00ff00ff00ffffffffffffff00ccccccccccccccccffffffffff00ff0000000000ffffffff0000000000000000ffffffff00000000ffffff00ffffff00ffffffffff0fff0fffffffffff00ff00ffffffff00000000ff00ff00ff00ff00
|0,11=>0xffffffff33333333ffffffff00000000000000000f0f0f0f000000000f000f000f0f0f0f0f0f0f0f0000000000000000ffffffff0f0f0f0fffffffff00000000fffffffffcfcfcfcccccccccccccccccffffffff0000ffffffffffff00000000f0f0f0f0fffffffff0f0f0f0fff0fff00000000000000000ffffffffcccccccc0000000000000000fffffffffff0fff000000000000000000f0f0f0f0f000f00ffff0000ffff0000ffff0f0fffff0f0033333333333333000000000000000000ffffff00ffffff00ffffff0000000000fffffffffffffff0ffff0000ffff0000000000000000000033333333333333000000000000ff00ff0000000000f000f0
|0,12=>0xff000000ffff0000ff000000ff00ff0fff0fff0fff0fff00ff00ff00ff0000000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffff0000000000ffffff0000000000ffffff00ffffffff000000ff0000000000000000000000000000ffff0000000000000000ffff3333ffff3333ffff0000ffff0000000000ff000000ff000000ff000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000000fff0fff000000000fff0fff000ff00ff00ff00ff0000000000000000ffff00ffffff00ffffff0000ffff0000ffffffffffff0000000000000000000000000000ff00ffff00000000ff00ff00
|0,13=>0xffffffffffffffff00000000fff0fff000000000ff33ff3300000000ff00ff00f0f0f0f0f0f0f0f0fffffffffff0fff0ffff0000ff000000ffffffffff00ff00f0f0f0f0f0fff0fff0f0f0f0f0f0f0f00000000000cc00ccccccccccccccccccfffffff0fffffff0ffff0000ffff0000000f000f00000000ffffffff0000000000000000ffffffff00000000fff0fff0ffffffff00ff00ffffffffff0000000000ff00ff00f000f000ff00ff00f000f0000000000f0f0f0f000000000000000000000000ffccffcc00000000ffccffccffffffffffffffff00000000ffccffcc0000000000f000f0f0f0f0f0f0f0f0f0ff00ff00ffffffffff00ff00ff00ff00
|0,14=>0xffffff00ffffffffffffff00ffffff00ccccffffccccffffccccccccccccccccff00ff00ff00ff00ffffffff00000000ff00ff00ff000000ffffffffffff0000ff0fff0fff0fff0fff0fff0fff00ff00ffffffffff33ff33ffffffffff00ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff00ff00cc00ccffffffffffff00ffffffffffffff0000ccffccffccffccffccffccffcccccccc00ff00ff00cc00cc00ff00ff00cc00ccffffffffffffffff0f0f0f0f0f000f00ccccccccccccffffcccccccccccccccc0000000000ff0000ffff0000ffff000000ff00ff00ff00ff00f000f000f000f0ffffffff00ff00ffffffffff00f000f0
|0,15=>0xfffffffff0f0f0f0000000ff000000ff0000000000000000000f000f000f000f0000000000000000f0fff0fff0fff0fff0f0f0f0f0f0f0f000000000ffffffff00000000f0f0f0f00f0f00000f0f0f0f0f0f00000f0f0000f0f0f0f0f000f000ffffffffff00ff00ffff0000ffffffffffff0000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x4030706281a051d080207010d04020706270e260408020706240402070625240e0d2304030206220508020706210e0d09042002061f0504080201000e051e04030207061b0504080207011a090408021906170904160207060508020706150e0d0913030207060504030207100d040c020b060a090408020706050403020100
|1=>0xd09040307063e1a05040302070104080207063b0e290904080207010504030207063a08020706392d0e370504080207060504080206360e35050408020634093304080207061a051d080219063205040302070617090408020730052f080206000e2e04080207062d0d23040302062c1b0504080219060d0904032a07060d09
|2=>0x60e0d0904080207062205040802190639260508020706391a051d0848070605040802064a0e49051d08020706090403160207060504084806000e050408020701390d0904030206000d4604030207060504080207450e0504080206440e2e040207064324420504080207060504030206001c4104030207064005040802063f
|3=>0xd56040f02060e050455080207060e0d2304080206340e1a0504084807060e0553080207060e0d040c0207060e2e0504020706430504080207510e0d09500408020706400d0504030207060504160207060e05040f4e0207060e2e05044d0802070605040807064c240e290408020706240e05040807063e240e4b05040f0802
|4=>0x43240d230403020b06600504030207060e0d090420030207060d2e23040f02060e0d052f080207060e1b0408020706240e400504080206220e090504080207450e0d0904200f020706050408020706391c04080207065e240e055d040807065c0e05045a0302070605040f080206220e0d57090408020706170504080206000e
|5=>0x206220e0504080207680e350d09040802070609040308670207060d0504030206000e0d0504080207450e18090403020706430d0504080206440e090408660207060e051d04080219064b05040308020b06650504080207060e170504080207450e652e051d080207060d0504080706620e0905040f0802061f090403020706
|6=>0x3020706740e170504080706730e590d090408020b0635050420080207060d7104080207060e0d09040207066f0e090504030207066f090504036e0207061a0904080207061c050408026d060e0d6c04080207060e6a0504080207060e05691d020706430e170504080207010d095f04030207060d051d040848070659050408
|7=>0x706430d0504087b07060e170504030207067a0d0904020706250e050408020706790e050403160207060e051d080207064709050403020706250d0504080278060e0d0904030207062c0d05040302070109040802070105040877020b060904080207062d0e050408020706390e260504080207060e290569020706430e0504
|8=>0x30207062b05040807065c0e0d09040807063e0e3505040f08020b062e0504080207060e0d04080207062d0e0d0504030706730e090504030807063e0504037e020706050403080207067d0d2e05044d0207061704080207062d0e0d090403020706140504080207067c0e1a0504080207010e260d0904080207062e05040302
|9=>0x207010402070643240e0504080206000e1c0d0504860207060e85050403080207061b0504080207061c170513080207060e05040f0802063f0e230504080283060e0504080207063f22170504080219060d0904820207060d23048102060e0d05040f0206220e09040802070612051d08800207060e0504087f07060e0d0904
|10=>0xe0d0513030207060e0d090403020706750d0504030219068b050408020706110d090403020706050408880706120d090408020706470504080206360e170d23040f02060e0d2e09040302070605040f080206340e0504084807060e0d09040207061f5935050408020b060d090487030207060d2e09040f0207060d051d0408
|11=>0x1f0e2e055f0408020706170d230408020b068f2e0504080207060d05048d0207060e1a0504020706430e172e0504020706431a0504080219060e050408028c060e5605044e0802060e1a051d080207061c8a0504080207060e5905040802063f0e8a0504080206340e1a0508020706390e050408070673240e0d5609040f0206
|12=>0x408020b062c170504082a07060e050408020706900e0d0504970207060e05040302079605040308020b063426050408020706631b0504080207060e05040308020706220d5604030207060d091d04030207060504080293060e0504030802070691590504080206340e1a052f080207060e0504082a0706900e0d0504200206
|13=>0xd05040f02063f0e0d0504032a07060e0d05049e0207060e3c9d08020706240e090504080207069b170504080207060e0d0904030207065e05040807069a0e0d09040f0206990e590d0904030207062e05040802070638410504030207066a2e0504080207060d5623040f02060e0d051d040802190604080207063d240e1705
|14=>0xd051d0802070647050408020706a80e1a05a7080207060e0905040807065c0e2e05040807063e0e0d2e0403020706248a35050408020706055f08020706390ea50504030207060ea4050403080207062e0504080207063905a20403080207063505040308020706050403080206360ea10504080207060e055f04a008020706
|15=>0x7060e0d0402070643240e2e051d0408020706170402070643240e290904080207061c560504080206340e2605040308020706175705040802070605ab04020706430e1a0508020706900e1a0564080207060e41040302070609aa0408020706090504030807067317050408020b063417050408020706220504030207066f0e
|16=>0xad080207060e260504080206000e0504080706620e0504080207100e050402070643390e0d0504080206360e178b050408020706052f080207060e0504030807069a0e17a40504080207062e0504080207066b650504080206440e3517050408020706170504080206360e0504020706432b0e0504080206000e63ac055f0802
|17=>0x70626170504080207062e0504080206000e1b2e0504080207060d0504af0207060e2e0504080207065e2e05640408020706051d040848070605040802ae060e5917050408020b060504080207450e65051d080207060e0d05040207066f0e0504080206440e090504200802061f0d05040f02061f0e1705040207066f0e051d
|18=>0x80206000eb42905b3080207060e0d090403020706990d05040807069a0e090403020706141705040807069a0e1a2e051d080207060504087b07060e0504080206000e470504080278060e0d050403020b061f2e0504080206440e05b2080207060e051d08020706390e1705040807063e0e050408020600b10e400504030802
|19=>0x504080207060e570504080207060e0d090408020b07061a0504080207060e470d051d040807063e0e090504080207061f490504080207060e2e051d040807063e0d09040388020706110904030207064017050408020706051d04080207011a0d0904030207061b0508020706390e05b5080207060e17050408020706470504
|20=>0x7060d0504020706430e560905040f0802060e0d0504080219060e29050408020706430e110d0904080207060e6aba0504080207060e090504030802070675050408b90207060e170504020706430e600504080207060e09040802070631050403080207063d0e0d2e0904080207060e0504160207060e050403080706730eb7
|21=>0x408020706c00e0504030207061c0dbf04080207060e0d052f080207060e051d080207065e0ebf050403080207060d0504080206000e050408020706be0e0dbc04080207060e23050408020706840e05040802070643581709050408020706580905045a080207060e172e0504030802070605040802bb060e0d2e051d040802
|22=>0xc2080207060e090408020706240e650504080207060e0d091d04080207060e0504082a07060e5605040308020706050408880706310504080706280e09051d0403080207060d05040f0206990e0d2304030207060e0d700904080207060e0504ad080207060e050486080207060e700905040308020706350504080207060e05
|23=>0x6a0504080207060e0d2e2304080207060e5905040f080206990e050408020706740e0504080207960e0d0504080207060e8e4b050403080207060e230504080206990e050403020706c40e0504082a07062b0e170d050408020706583c055f03080207060e2905080207065e0e0d5604080207060e110d0504088807060e3c05
|24=>0x4200802061f0e0d09040802070658050408020706c70e0d0504080207060e720d2e05040802070698050416080207060e17050408020706c60e562305040f0802060e0504080207062b0e63290d0904080207060e050408020706380e17050408020706990e29090504030802070605040308020706c50e59050408020b060e
|25=>0x50403080207061f4b0504080207061f0e051d04080207061c059d0403080207060e0d0904080207065e0e3c0408020706240e652e0504080207060e050403020706140e050408020706390e0504086e020706430e09050403080207065e590d0904080207060e05b304080207060e260504080207060e0d05c8080207060e05
|26=>0x60e59050420080207060e0d0904030207060504080207069c0e052f04080207060e0504080207067c0e05040308b90207060e17050403020706430e050497080207060e050408020706790e0504080207063f0e1a170504080207060e0d0403020706240e8a050420080207060e0d050403020706990e050408770207060e09
|27=>0x8880706d50e05049e080207060e050408020706d20e0d05040f020b060e0d2e0904080207060d050408d107060e050408020706cf0e1a0d0504030207060e17050408880207060e3505040f080207060ea10504ce080207060e0504cc080207060e050408670207060e0504080207060eca050408020706340e2e0504080207
|28=>0x20706610e05040802da060e050408020706b00e0d050403880207060e050408020706920e05d9080207060e5905040f08020b060e230504200802060ed804080207060e110504030207060e0d050408020706c50e050408020706d70e0d0513080207060e0504080207060e4717050408020706c50e0dd604080207060e0504
|29=>0x1c8a0504080207060e050408020706df0e050408020706de0edd0504080207060edc0504080207060e09055f04080207060e0504ad080207065e0e0504080207060e6b400504080207060e1a05080207062b0e17050420080207060e0d050408020706220e59350504080207060e050408db0207060e0504084807060e050408
|30=>0x50420030207060e1a0504080206000e090504ad080207060e0504a7080207060e3c051d03080207060e17055f04080207060e170d2304080207060e170d0504020706430e051d08020706940e3c040308020706240e0d0504200f0207060ee00504080207060e05040308020706390e0d570504080207060e17050408020706
|31=>0x207061c2305040802062c0e2e050403080207060e402e0504080207060eb805040f0802060e1b0504080207060e050408020b06e50e050408020706e40e056404080207060e0905ab04080207060e2e051d04080207060e09050408020b062c180504080706e10e56090504030802070605040802e3060e05e2080207060e0d
|32=>0x66317180904080207060e09050408020706c70ee7d60504080207060e1a0504080207060e1c650d0504080207060e0d0504082a07060e05040802e607060e170504080207062c0e050408020706902b0e050408020706900e05040888020706240e350d0504080207060e090504030207064305040308020706340e0d050403
|33=>0x2b0e0dba04080207060e05040308020706920e0d050408020706380e170504080207060e05040308020706d70e1a051d080207060e590d050408020b060e6a0d0504080207060e592e0504080207060e050408020706e80e0905b304080207060ea50504080207060e17050408020706140ea90504080207060e2e0504080207
|34=>0x8a050403080207060e0d051d04080207061c0d050403020706140e8a05040f080207060e0d050408020706390e260d0504080207060e059d0408020706240e17050408020706390eea0504080207060e3c0508020706e90ea10504080207060e05040308020706610e5623050403080207060504080207010e17050408020706
|35=>0x7060eec0504080207060e0d052f04080207060e17050408020b0706050408020706b60e18090403080207060504eb080207060e17050487080207060e050408020706250e0d0504030207062b0e0d050408020706790e0d04080207062c0e0d0504080207063f0e0d090408020706c60e051d08020706c1a60569080207060e
|36=>0x60e050408020706840e0905040f08020b060504080207060e9f8a590504080207060e29090504080706280e1b050403080207060e050403080207065e0e11170504080207060e0d050408020706340e050408028907060e055f040308020706a317050408020706340e0504080207060e12050408480207060e172e05040802
|37=>0x504080207060e052f080207060e2e050403080207060504080206000e0d050408db0207060e0d0504084807060e0d05040802da060e0d050408020706b00ea9050403080207060e17051d04080207060e2e051d04080207060905040308880207060504080219060e0d0504080207060e470504030807063e0e290569080207
|38=>0x207065e0eea050482080207060e05048708020706240e0d05e2080207060e1a0d0504080206000e59170504080207060e0d0504a7080207060e0905ed04080207060504080207060e8e1705040802070658110504088807060e8a0d0504080207060e8a170504080207060e0ddc0504080207060e0d0504080207060e6b400d
|39=>0x207060e0d050408020706900e0db804080207060e0504080207062b0e720504080207060e722e0504080207069805ef04080207060e1b0d0504080207060e1705040308020b07060d050408020706e40e0d056404080207060e05045b03020706240e1b170504080207060e050408020b0706240d05040802ee060e17050408
|40=>0x6250ea10d0504080207060e1a260504080207060e0d0504080207010e170d0504080207060e0504080706f20e1a0d051d080207060e051d0408020706240e172e050408020706a90d0504080207060e0d0504030207061f0ea9170504080207060e0504080207063f990e1a0504080207060e630d05040807063e0ef1050408
|41=>0x504080207060e54110504080706140e050408020706220e055d04080207060e170d050408020b07061a2e0504080207060e590504080206990e050408020706c50e0513080207060e051308020706140e4b0504080207060e050408d107060eea0d0504080207060e090504eb080207060e0504080207060e52090504080207
|42=>0x207060e05040308880207060e0504d0080207060e056904080207060ea3050408f40207060e56230504080207060e050408020706c40e05040f08020b060eba0504080207060e050408020706f30e055f04080207060e0d2304080207060e0d0504080207060e9f2e050408880207060e0d23040f02060e0d0904030207060e
|43=>0x4080207060ebd0504080207060ef6180504088807060e3c051d080207060e05042003080207060e0504080207062b0e0d050408020706990e050408020706140e0504080207060e630504080207060ef5180904080207060e09050408020706430e0d0504080207060e1c0504080207062c0e09050408020706c60e05ab0408
|44=>0xe050482080207060e0504080207060e31b80504080207060e0d050408020b07060e09056904080207060e0d050408880207060e050408020706750e110504080207060ef70504080207060e2e0504080207060e050408020706cb0e055f0403080207060e050487080207060e05c204080207060e1a0d0504080207060e0d05
|45=>0x6cd0e0d0504080207062b0e051d0403080207060e170504080207060e0d050408020706140e0d0504080207060e630905045b080207060e0d0504080207060e581805045b0807060e05040807063e0e05040308020b070605048703080207060e090504080207062c0e0504080207065e0e05040802ee060e59050408020706
|46=>0x20706240e0d051d04080207060e0504080207060ec12305040f0802060e09050403080207060e0905040f080207060e560504080207060e051d040807063e0e110d0504080207060e0d2e0504080207060e09050408020706c3bc0504080207060e5905040f080207060e05040308020706580d0504030207060e0504080207
|47=>0xe05045b080207060e0504080207060e580504080207060ec30905040308020706170d0504080207060e1a0504080207060e3c0569080207060e05c8080207060e0d0504080207060e98050408020706990e590d0504080207060e0504080207060e1c090504080207065e0e17050403080207060e050408020706e50e050408
|48=>0x504080207060e050408020b07060e050408880207060e0504080207060ebd3c0504080207060e0d0504080207060e0504080207060e98050403080207060e05040f080207060e051d0408020706
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x16f70b438585c2b4e15370a638515c27ce1377098384a5c244e11b708a38435c20ec100707cb83c9c1d6e0e4706eb8359c19ee0c87060b82e9c166e0ac7052b8279c12ee0907044b8209c0f6e0747036b8199c0bee0587028b8129c086e03c701ab80b9c04ee020700cb804d801ac0067
|7,0=>0x1b140d6a06a5034a81a140cea0666e32b8191c0c6e0628e30c818240bf205eae2ed8172c0b7605ab02cd8162c0af6056ce2ae815340a7a052d028e8143409fa04eee26f8133c097e04af024f8123c08fe046f022f8113c087e0430e21081044080203f2e1f180f4c078603b4e1d370e638715c37b01b580d73869a033d019680c74061a02fd01768
|7,1=>0x2a93952a0a86e53b8299c14ae0a48e51d728ac14360a0b04fd827b393ba09cd04de826b4133a098d04be825b412bdc950e4a1724cc1249c9150483723dc11d1c8d90464822e4115208990444821eb90d6085b0425820ec1056081b040581fec0fd607db03e581eec0f56079ce3c681df40eda075ee3a961d138e6a0725038a81c140dea06e5036a8
|7,2=>0x3a441d020e710730839441c820e310710838441c020df106f0837441b820db106d0836441b05cd7306b18354c1a89cd350692834541a0a0cf5067283354198a0cb8c6548326419120c7906357316c1899cc3d061683074181a0bfd05f682f74179a0bbd05d682e74171a0b7ee5b782d7c169e0b3f059782c7c161e0aff057782b7c15a1cac2e5598
|7,3=>0x49e424d5d25b0925848f3a45a121d0906847f423da11dd08e6846f4235a119d08c774603a2e21162e8a98450c2269d125088a8441421ea10e5086b74323a17210a9084c8422ba0f6106b082d8412c2076102b080d8402c1ff60feb07ed83f2c1f760fab07cd83e2c1ef60f6b07ad83d3b1e81cf31079083c441e020ef1077083b441d820eb107508
|7,4=>0x138f09bf84dbc26c1d35109a174ccc26461314e98284bd425ca12d5096284adba54e129709447
|8,0=>0x5ebbaf3a578b2bbd85dac2eb617492b9b95c9c2e2e17052b7a85b942daa16c32b5a75a942d2dd688eb3b9599c2cae16452b1a858942c2656030af985793abaa15c50ada856942b2a15850aba8558caaa615412a9795474aa1dd4fd2a768536ca99614b92a5395254a90654730a318514c2889d4332a109504ba80613f309f184f4c278253af29cf8
|8,1=>0x6f9437aa1bc50dda86e94372a1b832db896d7cb69a5b3d0d9686c74361a1afd0d7596b73b59a1abd0d5686a6cb5125a790d3486964348e5a370d129684cb40619f12cef9673c337a59ab2ccd86624b2f219690cab96514b26659230c898640c31e618e30c6986304b15e589f0c46961ecb0d258572c23860d4b04658112c0085fc42fbe57cd2bde8
|8,2=>0x8024bff21fe90feb97f14bf6a1fa50fca87e143eea1f632fa897d043e621f1f2f8877c0bbde25ee10f6797afc3d5a5e9b2f44979dcbcce1e552f21978cc3c425e0f2eff877bc3bbe1dcf0edf876bc3b3a5d8b2ebd875ac3ab61d492e9b97494ba2a1d06ee7b873a3b9b21cc72e5b872a3b92e5c870e3c771a438ae5c470e1b8709c382a5c050dfa8
|8,3=>0x9144487e642d320e8903447f663eb11ec98f24477223a911cc88e1cc6ee236531a998d0c4662631f318878c0445de62dd316598ae4c54e62953141989c4c4c222511120888bcc43a620ef0fe987b443b661c930dc8869cc32e218530b998584c2a2213f309788474c21a20fd107598364c18e60b530519824c41062071302f9813c407a602b300d8
|8,4=>0xa254d106687314309a13cd07a682b340c9a0244ff227e733eb89f14cf6a27a513ca89e0ccee2675f33a699cecce526719138489bdccdca66d3336189ac4cd3e668d333e899b44cba264d131d998a4cc2e660532f999793cbaa25c6f2da996944b2a258332b89957cca9e253d329779474ca1a24fd127689374499a24bb32549925cc90a647332309
|8,5=>0x15189a87cd421ea0114f88a78453a229c114d79a674d31a297d14b77a57c529e2940f4979a474d21a28fb34749a35cd18e28b534537
|9,0=>0xb974dc9a2e3d17159b86c5c162dfb16f49b75cdb8e2db536d19b644dafe6d6f16b07b5445a7e6d2d368e8b43bd9fe2cef166f8b33c597a6cab364c9b22458f22c69162c8b124586e6c27160b8b014d7e66be315e98af0c57626ba115c79adfc56de2b5f15a78acf4d6566b1b15849abe455ce6ad715629aad455466a9315418a9cc54c62a5315218
|9,1=>0x17df8beb4df3a2f8d17bf7bdb4deba2f4b379d8bca4de2e6f07177b8bb94ddaa2ec517599ba84dd222e8117379
|10,0=>0xc1fc60de305f18278c0fc605e301f18078bffc5fde2fdf17e78
|11,0=>0x18477
|_,_=>0
def wAt:=mkWire dB 248 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40e42039061c4343805084f491050380cf2050441439061c4343808054b8e10d0ec3476040e43411040e41c710d0e01421063146038050241439022b43413050e420392902c20390409414390d0441039061c434380508420150d1d41039061c43438050e43438080546038050241439050e41051080e4340b061242039110e03409050843c24070e4143905084201d
|1=>0x50841151140e0340b050843c24050e41421080745c230d0e4343b0508419492b0e034130508424730d0e014390d0ec2049110e0340905084213d090fc143908074f039050382039051f43c390d0bc1c39080543411040e408710d0e01421061c434381704c3439050e4681f080e434110547468380d044681f0d0e03411051242039110e034090508420391d02c1439
|2=>0x5084343b05085900b04634343a050381439070e4203908054141d086140c8e080e4141d050e40c1d080e414210d0ec201d08054141d0447468380d044140e055f4203907224342f070e414211b06c20a5040943c39050e4201d0d0e05c130d0e4110d0809814395b0901439080242039590bc143d070e43563070e88c390507414210807434390805408710d0e03411
|3=>0x50e5c0230902414390809814390d0e03411080541d51140e0340b0508414e10d1d810390805435ad1a0e814210809814390d0e418710d0e01421050e41421040342039040e408710d0e01421050f41951140e0340b05085643b0d0742015180302039050e4681f080e434111b06c68390d044242305025941f2e044343b071c410390d0e01421051f42039170ec3439
|4=>0x170ec5c23050342039027943477040e56c380802420392908c1025050e4e43b0d0e41421110303409040e468380d0441421082981025050e41dad1a0e834110907c2039050e42015080e418710d0e01421050e418710d0e02015032302039070e4141d1b05c20a50409414390809814390876815d5080e420150f0e5643b050f4201d05724ac3a0d04c20157008c2409
|5=>0xd0bc1c39050841439110e03409080541039033c0141102524ac380d04c14210d04c1439080e414215d02c110d08098143908054740b050e41039050f4201d1b05c68390d04420155f02c1421040342039050e4740b080e41039031cc20390d0e01421610e40c8e080e4141d05084157e05034100d080e41439080e4340b0508418710d0e0341105084683b0d0442015
|6=>0x8056281f200543c39080740a250d8801421020e41439080540c1f080e4143d080740c09050e4203905084343b080741039061c43438050845c17084342026050e4681f0d0e0341105084211d1a0e03411050852c3b051f40c1f080e468390d0e03411078440c8f080e4141d220e4342f070e414210d0e41c710d0e01421080541439085841c3a0f0ec201d08054141d
|7=>0xd02c14211708c3439050841c710d0e03411050841c49110e034090508410390d0e03411050845c1d1707c34390508434111704c343905084241d050e41051080e4340b0508414390302c2039050842039071c4343805084b98d0d0e8343b050843409050e42039050840839110e034090508414391a0e020151b07c3475040e414210d0e42015050742039050e4343b
|8=>0xd984343b050848c39050741421040e41c710d0e01421050380cf2050441439086b4683a0d0441421067a56c380802420390503420390d0e8683b0d044b8750d0ec103905084d03b1707c140d080e48c39080e42015050741039050e42039050841e55940e8f023040564839031881409080e6281f590e4143d080743438050845c3b0503420390d0e42015088e4503a
|9=>0x40e434115d02c110d08098343b050382039590ed6439050f4201d1704c140d040342039080e422993c0ec10155fa3c143a04036283b032342039050746c1f055f4100d022b43413080e4227d110e8340905084140e080e67039096982011050e42039050841026050e46c0b0d1d4103905084341f050e4341d050e4203905084343b0d1d81039057a56c38080242039
|10=>0xd0e411492b0e03413050846c0b055f4100d2e044343b05086283b170743439050845c170d0e45c3b0d0e414210d0e02015040941439090745c1f0809414391b0ec157d040342039570e4356305084341104634343a0508415e95b0e02009080e424c7180e01409050e414395f02c100d080e43439050845c2f0d0e41421a908c5c09050342039040e468380d0443474
|11=>0x50841049110e034090508410391704c34390508414210d0e4683b0d04414212e1d4343b0508422c10d8881421020e40871040e43438050841d492b0e03413050843439050846c1b0d1d414212e044343b040e41421a908c44390d02414216507cb8110d0ec14210f0e421c2080942409050e5900b04634343a050841849110e03409050846c1f1a0e43411171cc3438
|12=>0x5084740b040e41421050e40c1f080e468730d0e014211d02c343b050840839050e42039050843409050e42039050841871040e43438050843411050e42039050845c111704c34390508412d92e02c343b0508400381a07c14210904425a408044341f050e42039050846c0b1a0e43411050e4340b080e414210d0ec1421027943477040e41421050841dad1a0e83411
|13=>0x503420390731460380502410390d0ec14211708c343905084241d050e4201d071c43438050842026040941439050e4340908056e82105984103a0302c1439080e40891050382039084342026050e6e021230ec141d180e01409050e40cf2050442039050e4343b0805420c5180e014095f02c100d080e4443b0d02414210d58c1c3a050841439070e420151a0e03411
|14=>0x1d0541039050e42039040e4341f05084201d080e42015050742015090241439085e41026050e423053c0e01015080e42409050e5643b050f4201d4d05c2261040e820390d0e01421055841c3a0805410710d0e01421040e41026050e42039055841c3a1a07c34110508408920503820390508416f5020e80c8f080e41c3a080981439050e41c3a095b02009050e45c3b
|15=>0xd0ec201505075641f050f4201dbc08c16f5020e819e95b0e02009140e8340b05084147d0307c20395907c208d050756c17080242039022b43413050841c3a0d0e4142105044100d080e41179040981439230e420150507408390d024142105044130d080e814390503820392e044343b050841439040e42015022b43413050848c39080e4141d180e01409020e4a40b
|16=>0x1704c3439050842026050e42039040981439050e4341d0805425a40804414391a0ec3411050841421045841c3a071f40c1f080e41c3a050e42015085e81026050e4ac3a0d04c1421040e8343b0508420c5180e01409050e4201d230e4141d0d0e834130508420150409414390d1d81039050841421080e41025050e45c0b050342039050f41c39080743661040e81421
|17=>0x80741439080e41421096982011050e410710d0e01421940e4f0230405408910503820391708c140d080e423253c0e810150d1dc10390508664390d07c14210d0e4341105084140e080e414210f0e4201d080e4341f050840c8c080e4141d050e40c1f080e40c1f080e410390d0e0142104244140e080e4142104098143905044140e080e4343b05084340b080e41421
|18=>0xd0e41421058782221020e410510d02c14211a0e0341105084343905084158d0d0e820151808c1409020e42351180e81409d30e4143e080741c3905084201d050e4343b0805408730d0e0142104d08228d050e820390d0441421050342039590ec143d0807422f5020e823351d05c1039031801409080e72c3a6905c10211707c3439050845c3b0d0e414210f0543c39
|19=>0x50843663040e81421081d41439040e41026050e4683a0d04414212e074343b0508434130d0441421050340c1d080e4342f070e41421590ec143d08074098d0d0e81421021c43438050840c8e080e4141d071cc3438050843622050840839050842039020e40c62050242039047a56c3808024143d070e4201d080b41c390507415eb5b0e02009080e43409050845c0b
|20=>0x9074143907c94f03a0405410730d0e0142103074203905084681f0d0441421085e41026050e43474040e41421050442039040e4140d0403420390d0e42015050745c230d0e414213c08c1015040e40c170504420390f0e414210807417850888808391704c140d080e43563070e814210d0e0343905084243d050e4201dc40e4156e08024160a085841c3a2e024343b
|21=>0xd04c1421074342026050e424210907c14392b0e4341305084ac390d04c1421020e4140e080e5643b0d0741421080e42026050e45c1f0503420390d0e0203905085581f230e4141d170ec140d080e4343b050848c3b08074141d0d1d4103905084208e070e4141d140e4340b05084118d0d0e81421690ec2011050e4343b050841c390907c1439088881409020e42039
|22=>0x61c43438050843439050841661040e82015031881409080e43476040e414212e0e4343b05084161e0302420390d0441039050841c390d07414210d984103a05084343b050855823230e4141d096902011050e422993c0ec10150d0e4340b0508444390d02414210d0e8343b0508424210502414390969c2011050e4170d080e834380d04414212e044343b0508408ad
|23=>0x902c1439050340c09080e420a61d05410390d04c2039050843477040e4142105084241f050e664390d07c14210902c14390805410393c0e0101508044f03b040540c8d080e4141d0d0e010390508420390d02c1421200543c391704c343905084683b0d04414210503820390d0e414210d5841c3a0508410151d08c1039bc08416f5020e80c8e050742039230e4141d
|24=>0xd04414211d02c2039040e424110804414390323c2039050741439070e4201d110e8340905084143d08074a40b040941439055f4100d080e420390409814390d0e43409050845c1f0d0e414210d8801421020e4143a0403420390d0e41421110e034090508408710d0e014213cc3c203a0405410710d0e014210d0e41c3905084b80b0d0ec1421080e41409050e42319
|25=>0x40e4142109c3c203a050e4503a0d02c14210d0e41c3a0508408390d0241421590e4341d050843439050843663040e814211a0e8341105084b81d0d0ec1421041c43438050845c3b0503420391a07c341105084098d0d0e81421021c43438050841c730d0e014210d8881421020e45c090503420390d0e414210d0ec1039050841439080e40839071c43438050846838
|26=>0x5084740b040e414210dbdc083a05084ac390d04c1421230ec201505074ac3a0d04c14212b0e8341305084343b040e8142108f04128d050e868390d0441421050342039070e450390d02c142104634343a050840c17080242039170443439050841c3905038203907984103a050841439085841c3a050382039041cc343805084681f0d04414210d0e4341d050843474
|27=>0x50845c0b0d0e4142104144340b0508410510d02c1421051f40c1f080e408730d0e014210d5841c3a0508423190902c14392b0e034130508420a60409414390dbd4083a05084683b0d0441421061c4343805084b8390d0ec1421f002c128d050e810390d0441421050382039040e434390d0ec1421110e434090508420150307c20390d0e414210d07c14210d0e83411
|28=>0x80241409050e42026050e4343805084241f050e4240b050e5a43b040842039020e4228d050e8143a040840b0d080e88c3905074156e080241c39080741661040e81622020e47421040e4201505074443a0d024343b05084201d08054141d050e420390508450380d02c14210d02c340905084342f070e41421044342026050e41c390d0e414210d0ec14210d074341f
|29=>0x8024740b040e42039070e40c09080e4241f050e41026050e41e61040e8143d080742161070e86038050248c3b050741c39050842011050e41421020e40c0b080e4340905084603b05024343b05085a41704084100d080e42221020e4130d080e8341105084083a05085a43a040841409020e41015040e40c1d080e4341305084341f05084340b05084343a050856c3a
|30=>0x40541161070e8103a05084341f05084341d050843438050841026050e4140d080e4208e05074140e080e4103905084f03804054141d080741439080e41439080748c3905074740b040e4340905084343b05084203a050e416f5020e8143d080742039070e82039050847417040e43413050842039040e4343905084340b05084343a050842009050e41c3a050841409
|31=>0x1c39020e4083a040541421040e82039080741039080241c3a080e81439080e43439050843411050841021
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x159400000000000000029204e40966000000000000000120c21a800007e80ed01ba03340000000017a000000000000152800004c800000000000000008900f201950000000000001810000000000000000288044c0718000014801540028000
|7,0=>0x20c840907f98fc31f623dd079a0ef41d863a887320e241bc837446ca0d631a66340c6698cb2190600006220c2217e600005e90ba300002e085a20b0415882a105298a2313c826cc4c189530000248c47208b31124000042a000010641fd03da07740e681bd036186b10ce818d000000000c0600002f105b3
|7,1=>0x39a8728ce321c3337e86ed0dba1b3436246b50d591a74346867d0cda197432860000000190431886210c2218042fa65e50bb197242dc85a90b32164200005810ae215842a885410a7894b428e80000a1a140327884e4c9b1933326064b889521273248648108e2118422884410000000021c442cc00010a1
|7,2=>0x4e889c11362000000009a4d32a26230000000000025f34b6896492aa00004a2893512592474488690111e9a3a346c88ccd190800000008b91152228244a688510ea219442a8845106a209440e40000000204340440000ff21fb300007dd0f9a00003de800000001eb43ce80000f291e143ba87650eaa1d14
|7,3=>0x6062bfd000000005f68bdd00002f610000bc900002ef35d6800000002e745c68b8496f1ada45ac8b4900002d1159a800000002c9458a80001611abf35768ae0c000000056a6ac500000000000000015792ac30000aa115222a0453a60000000299452a8a45146a28b25106a11140980004fc69ecc0002783
|7,4=>0x19b1b33365e8cad000032746468c7d18da00006306c54d88a30e3614800018413044
|8,0=>0x7e86fc4df71beb37d06f94df11bdf37b86f64deb1bd337a06f34de51bc737886f04ddf1bbb37706ed4dd91baf37586ea4dd31ba337406e74dcd1b9737286e44dc71b8b37124e18dc2138136fc6decdbc1b7536e46dbcdb61b6936cc6d8cdb01b5d36b46d5cdaa1b51369c6d2cda41b4536846cfcd9e1b393
|8,1=>0x954729ce521ca1393c726ce4c1c9629267244a471c8b39107214e411c7f38f871e4e3b1c7338e071b4e351c6738c87184e2f1c5c28b27158e299c51289c712ce241c4538865100e1e9c3b287070d4e191c2f385870a4e131c2338407074e0d1c19182c704ce081c0d38183024e031c0338006ff4dfd1bf73
|8,2=>0xacc758ceb01d5d3ab65560eaa9d523a9e7530ea49d472a887504e9f1d3b3a7074d4e991d2f3a5874a4e931d233a407474e8d1d173a287444e871d0b3a107414e811cff39f873e4e7b94f439e273b8e759ce839ca7388e6f9cdc39b27358e699cd0399a7328e639cc4398272f8e5d9cb8396a72cca581cad3
|8,3=>0xc367860f0b16133c2060003069e0a3c0e7810f009dfe3bf677e0efa9df23bde77b0ef49de63bc67780eee9dda3bb05754ee91dd02b9c572cee41dc53b865700ede9dbb2b7076d4ed91daf3b5876a4ed31da33b425678ecd9d983b2a7648ec79d8c3b12761cac21d813afc75ecebc1d753ae475bceb61d693
|8,4=>0xda47b3cf661ec93d8c7b10b6116bf3d787ae4f5b1eb33d607ab4f551ea73d487a84f4f1e9b3d307a54f491e8f3d1c3a30b4516873d087a04f3f1e7b3cf079d4f391e6f3cda59a8f339e643cc27978f2d9e583caa7948f279e4c3c94591cf221e413c7c78ecf1c1e353c6478bcf16962a3c4e7890f109e1e3
|8,5=>0x71b2e325c58f899f103e1a7c28f839f043e045bfcf7e1ef93dec7bccf781eed3dd47b9cf721ee13dbc7b6cf6c1ed53
|9,0=>0xf365e64bcb97952f265e44bc7978d2f165e24bc397852f065e04bbf977d2ef65de4bbb97752ee65dc4bb7976d2ed65da4bb397652ec65d84baf975d2eb65d64bab97552ea65d44ba7974d2e965d24ba397452e865d04b9f973d2e765ce4b9b97352e665cc4b97972d2e565ca4b9397252e465c84b8f971d2
|9,1=>0x7c52f865f04bdf97bd2f765ee4bdb97b52f665ec4bd797ad2f565ea4bd397a52f465e84bcf979d2
|10,0=>0xfa43f447e80fcf1f9c3f347e60fcb1f943f247e40fc71
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x612000000c180000018200000030000000045000000081c000001008000001e0000000382000000420000000830000001040000002040000004040000008000000008000000002e000000050000000098000000120000000200000000300000000500000000800000000e0000000180000000280000000400000000600000000800000000800000000
|1=>0x400400000800000000de38000012860000021820000042180000084200000108200000210000000401000000800800000bcf00000178e000002e3c000004ef8000009cf00000103e00000205c0000040b00000081000000100c00000200800000400800000800000000e08000001c0000000304800000602000000c00000001010000001c780000030f
|2=>0x57ce00000af7c000015eb800002bcf00000578e00000ae7c000015cb800002b8f00000561e00000a77c000014e780000281400000502000000a018000011f38000023c300000472e000008c3c000011810000023000000044ce000008824000011038000021c50000042140000084200000108300000210200000410800000802800001003000002003
|3=>0x1100c0000220080000440000000830000001000e0000200100000400100000800000000df1e00001af3c000035c780000660000000c40200001880000003084000004d8f00000979e000012e3c000021c7800004106000008204000010018000020010000040000000077be00000ef1c00001ceb80000399700000610c00000c20800001800000002bef
|4=>0x2961a000050e3c0000a18100001418200002820400004ec1c000095c7800012b2e00002561e000048c5c0000918100001070200002060c00004082c000081030000102000000202040000400200000800180001000200002000000002ef7c0000584300000abc500001571e00002a73c000054c380000a0070000117ca000022f14000044ef800008816
|5=>0x10610800020af1c0004094380008108600010200c0002008080004000100008000000008778e000106f1c000208410000410800000800040001000000001d5c780003830600006860c0000cae3c00018183000026bcf00004d71e000092f3c00012082000020b8f000040c0c0000808000001008300002000000003571e00005af3c0000b5c7800016306
|6=>0x90010c00110c71c002218e080040808000080378e00100471c002005e38004000000006053be000c0a57c001014ab8002009df0004010200008020000010000080010a9cf00021508e00042004c000840000001029df0002013be00040207c0008040b000100804000200008000400000000608430000c108200018178e00020ef1c00041ccf8000832c7
|7=>0x20013be004000f040080008300100010200160102600280a77c0050142b800a0081700140102c0028020480050000b000a00013001400004002420000004814af8009028160012013be00240207c0048040b00090081200120100a002400058004014ef80080295f00100508e00200a048004010000008009df00100102600200004000241de3800481086
|8=>0x2040604004041c0000805ccb80100abc700201571e00402a73c0080540780100a10200201402e00402800c008050010010088000020102040040200d80080400380100800400201000400402000000801def801003bc700200602e00400af3c008015e3801002b8f0020053be00400a5740080142380100280f00200461e00400871c00800dfd801001086
|9=>0x800041000a00205c0140000880220294f00440502400880a008011010080022009df00440102400880201801100400002200012004400008008800004010854ef80210081f00420102800802af7c010054af80200800700401000200800a77c0100140a00200080600400000200800000000c0142780180081d00240530e00480801c00900002801100817
|10=>0x1100129e02040203c04041ccb80801010801001736e02002e65c04005c0b8080039b701000732e02000c2080400180b8080029870100042040200082080400100b80800201001000378e02000671c04000942008000d8f01000171e02000277c0400040b008000810010001000020000c100400008400800010201000002002000001c04000002008000002
|11=>0x400000000600884380c0105c7811000b8f02004979e040092e1c0801248101002430a02004851e040088418080105c381002010e0200402180400508340800a0c201001030602002060404004041808004183010004bcf02000971e040010e3c08001000010000b8f02000041e0400000080510140900920000701200000602240a058044804ef808900147
|12=>0x10010778e20020af1c400401e3880043bc710008638e20000ef1c400019e3880002bc710000448e200006f1c40000ce3880001086100002004200002f1c40000001048441bc709001400e12000e65c240015ef84800298709000400e1011042182022084104004000208000610410000af1c2000084104000108004002538e08004a31c100005c3820000100
|13=>0x510002f8fa0002d31f40000a63e80001487d000018c7a0000131f00000e63e00001c87c00002d8f60000778e301100208600415e3880441bc710088268e20100ef1c402018e3880401bc7
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x240000000000406010000000000082e00030200426000000400000001200010000000000180c0900000000b000000000010200400030601a00
|7,0=>0xcb8440337208a492e31f37e828f95880287e01000002900c45cefb0614004010f0047e3e0000c44060780c7c011e000856903008096611808e68c010aeb7011781400005337000e2938fd66b95c028328d08a9a24ad0982c96e51c8100461012c92c7d040002c020000a7a03648b40411008118e0200041b40202001e80069024022e0086c0cc6240a4000008800500e
|7,1=>0x34004f0001d848017f00004001101800009a008b27e1f0180416f21a800000128800050f0080a1c0014004000000000f2110009da2038a000004a413f80c281400c0400010100006990040e780000806020022e4d41018700e000a80680ed0122022f6478098c000010106280109454e34880c0601040019a1169800861100108340004800013200801e63631d641f8a
|7,2=>0x2c115db740098ba0040200c001056025e8011c01
|8,0=>0x2db2d958b2da1ee6372a4415cb72c0c6af292e2a0b168701ecb06ea511a5933a4958fe7a4bac1f821a2b0064370abb0b06ec133a4a75a98fcb6d87a892de99a1dc074f18dd25d7092fd48ff5fd09c22aafb93e34c7585d2d2bab7ce636093af4f9886e2c314628745416ae9f67dd4cd02144121f943d97489647bd5e3f898998db72172424d8412dea324556a9c538e7
|8,1=>0x5f250505b2dc38b1449e0f737961cdae8c9d90594c47636bcd1f4d69112ec7c08c693d1c01398c09081e4d371d6f9d5d918a4350d96b5d65aa38554c789d7ea63fd9072372d5e12215d6a4884a3bb8dce8c9264d44c83675ee5a1a4bef4fd4ca803b37b19d42b2f61854a5179c3650c3d2c29cd258a55de502d2996d82e4182f97eb6d3baa60336f18b414e2c0deab99
|8,2=>0x21bbbcc85bd18c6f93bae5807baccaa04671580162dd1538d622daabc5b684b940612a047d696ea73e3a1609c77494daac4d4487e5a4f524416858bc94cd70b2dc6733349a904856232e3f0238ae95723880e15d785922ea6d52a6b16e7371b3a970f3a
|9,0=>0x5caa5ecdf832c52ac25e84215c92e50971df1d6bbeb5f90c643612ef68179454b5197a9f57d11572dae953860e762cbbd0c5b7495957a5cd693398d552c744a2bee18b99a3b4c4df4acb178b79c91e3a0f0c5630914abcfbeb40cc8567958e4
|10,0=>0x2b678b76c1a170bccb51680aa67
|11,0=>0x34
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 35 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 10 roots_126 ops++addP pm 1 dom_119 9 roots_119 ops++addP pm 2 dom_95 9 roots_95 ops++addP pm 3 dom_109 8 roots_109 ops++addP pm 4 dom_61 7 roots_61 ops++addP pm 5 dom_62 7 roots_62 ops++addP pm 6 dom_121 8 roots_121 ops++addP pm 7 dom_123 9 roots_123 ops++addP pm 8 dom_111 9 roots_111 ops++addP pm 9 dom_107 8 roots_107 ops++addP pm 10 dzo_43_4 5 roots_43 ops++addP pm 11 dom_125 9 roots_125 ops++addP pm 12 dzo_59_4 6 roots_59 ops++addP pm 13 dom_63 8 roots_63 ops++addP pm 14 dzo_111_16 7 roots_111 ops++addP pm 15 dom_55 5 roots_55 ops++addP pm 16 dom_43 5 roots_43 ops++addP pm 17 dom_103 6 roots_103 ops++addP pm 18 dom_91 6 roots_91 ops++addP pm 19 dom_59 6 roots_59 ops++addP pm 20 dom_117 6 roots_117 ops++addP pm 21 dom_29 4 roots_29 ops++addP pm 22 dom_115 6 roots_115 ops++addP pm 23 dom_93 6 roots_93 ops++addP pm 24 dom_31 5 roots_31 ops++addP pm 25 dom_53 4 roots_53 ops++addP pm 26 dzo_110_16 6 roots_110 ops++addP pm 27 dom_87 5 roots_87 ops++addP pm 28 dom_79 6 roots_79 ops++addP pm 29 dzo_109_16 6 roots_109 ops++addP pm 30 dom_83 4 roots_83 ops++addP pm 31 dzo_123_4 7 roots_123 ops++addP pm 32 dzo_107_16 6 roots_107 ops++addP pm 33 dom_99 5 roots_99 ops++addP pm 34 dzo_107_4 6 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_111_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_110_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_109_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_123_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_107_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 10 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 53 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 274 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 274 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 345 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 89 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 345 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 85 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 10:=lower_slice_b [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_190
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_222
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,64,68)] (by decide +kernel) lowS_235
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,1,17)] (by decide +kernel) lowS_235
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003332000033330000333200003332000032320000
def gsh_237_16:=0x333300003333000033330000333200003333000033320000333200003232
theorem lowS_zo_237_16_232:Lower true dzo_237_16 roots_237 gzo_237_16 9:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x222200002222000022220000222200002222000022220000222200002222,0,1),(0x303000003030000030300000303000003030000030300000303000003030,0,4)] (by decide +kernel) lowS_232)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,96),(64,192),(80,81),(80,84),(80,88),(80,112),(80,208),(128,129),(128,132),(128,136),(128,160),(128,192),(144,145),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
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
|4,0=>0x8f79b0465a
|5,0=>0xacbd8a2cba5cf5e54dde21b20
|6,0=>0x91c917221b4789a3ef5d2adf9255231c7dc11654
|7,0=>0x76c3675ba7736236705366eaa64cd75b91050dc85034e4f2cd49def48a204836045c553be6f3a3ee39c1939b0238edd34018326a530d232a756281352549d2143420a49204111e13f1da131acff19dd019c57197631382512cc10c74809efb045a0041100383e0152d
|8,0=>0xee7afad084a493992fe48563884c068499b83ec081d737ea7e7a583734b36e20561e6c5f93c5c474592ac502b549ba2495e148ea941a6d3c56d3b2713a1b3391243813c3720d36ba035e2f33365332a72ab6d23d4b1f3061b0811936b183e914596138cb138251284b103c00d6b50c7550b8dd0a134056b2024100182d
|9,0=>0xc027bbca6367cdb642ba63888506e4425e33db003ca6b34d4729dfc1f08c1c1b2152a613b710c908059bd
|10,0=>0x7762c66f6a470633f699
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000003333333333333333333333333333333333003300330033003300330033003300cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333300000000333333330000000033333333000000003333333300000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc03333333333003300333333333300330033333333330033003333333333003300ccccccccccccccccccc8ccc8ccc8ccc8ccccccccc8c8c8c8ccc8ccc8c8c8c8cb333333333333333332233223322332233333333222222223322332222222222cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000003333333333333333333333333333333333333333000000003333333300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003333333333333333333333333232323233323332333233323332333232323232cccccccccccccccccccccccc88888888cc88cc88cc88cc88cc88cc888888888b333333333333333330033003300330033333333333333333300330033003300
|0,1=>0xcccccccc000000000000000000000000cc00cc03333333333333333000000003333333333333333333333330000000033003300cccccccccccccccccccccccccccccccccccccccccccccccccccccccccc00cc03333333333333333333300003333000033333333333333333333000033330000cccccccccccccccccccccccccccccccccccccccccccccccccccccccc00000000000000000000000000000000000000000000000333333330000000033003300cccccccc00000000cccccccc00000000cccccccccccccccccccccccccc00cc03333333333333333333333333333333333333333330033003333333333003300cccccccccccccccccccccccccccccccccccccccccccccccccc00cc00cc00cc0333333333333333333333333330033003333333333333333333333333300330000000000000000000000000000000000cccccccccccccccccccccccccc00cc00000000000000000333333333333333300000000000000003333333333003300ccccccccccccccccccc0ccc0ccc0ccc0ccccccccc0c0c0c0ccc0ccc0c0c0c0c3333333333333333330033003300330033333333000000003300330000000000cccccccccccccccccccccccc00000000cc00cc00cc00cc00cc00cc0000000002222222222222222222222222222222222222222222222222222222222222222
|0,2=>0xcccccccccccccccccccccccccccccccc0000000000000000cccccccccc00cc0000000000000000033333333330033000000000000000000333333333300330000000000cccccccc00000000cccccccc00000000cccccccc00000000cc00cc0000000000000000033333333333333330000000000000000330033003300330000000000000000000000000000000000cccccccccccccccccc00cc00cc00cc0000000000000000000330033003300330000000000000000003300330000000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000cc00cc0000000333333333333333300330033003300333333333333333333003300330000000000000000cccccccc00000000cccccccc00000000cc00cc0000000000cc00cc033333333333333333333333333333333333333333333333333330000333300000000000000000000000000000000000000cc00cc00cc00cc00cc00cc000000033333333333333333333333333330000333333003333330033333300333300000000000000000000cccccccccccccccc0000000000000000cccccccc00000000000000000000000000000000000000033333333330033003333333333003300cccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc0000033003300330033003300330000000000330033003300330033003300000000
|0,3=>0xcccccccccccccccccccccccc00000000000000000000000000000000000000000000000000000003333333333003300
|_,_=>0
def sP:Nat→Nat
|0=>0x40d6440c92d034c2830492cd30a0c044b40c50a0d724b40c5840c024b4053c33922d020304b34c20344b4052831c624d30a0c624b15550a0c92d02834c94052830402cc2031c634c3c318e2cf0c71893080c12c52831c62452031c61440c2040
|1=>0x5840ce2d03553c40c92d03623c300b40c60f0c038b40c6c428300e2d058810324b4055952a124b40d6083c300b40c54810324b40d10324b4201483c338b4052832522d014f28324b41e31654a0c92d015d28324b40d31429c24b40c21b3c338b
|2=>0x9092d034c20f0d72d03080d12d034c21429c24b40c59828324b4056ca0c038b4152833892d03583c35c92d03152a10092d034811c38b40d59428324b40c50428324b40575428324b40c2834c940d3088c338b40d2040d738b40d58f10324b405
|3=>0x24b40d75628324b40d31b2830092d031d28324b40d30a0c92d0a0d31810a7092d034c28300b42734c88a0c02d034c2047092d034c60a0c038b40d3082a624b40d31820a0c02d034c2833892d094d30f10300e2d058a0ce2d015654a0ce2d034a
|4=>0x2830092d034c60a7092d034c3c40c024b40c58a0c92d014c20f0ce2d034c2832522d034c59528324b40d31528324b40d31928324b40d30f10324b40559b28324b40d30a0c92d0a8d31d6ca0c92d034c60f0ce24b40d30a0c92d0a4535b10a0ce
|5=>0x20a7092d034c58828324b40531520a0c92d034c2040ce2d034428326c2d035660a0c92d034c58a0c024b40530810324b40535d20a0c92d034c50428324b40d30a0c92d0b4d30f2835ce24b40c21b10324b40d3082835cb40d308283b0b40d31d
|6=>0x24b40d30829c24b40d31b28324b40d31628324b40d3042830092d034c10a0c92d014dc4a0c92d034c10a0ce24b40d2835c024b40d33028324b40d30f2833892d016f28324b40d31628338b40d30a8492d080d32e2a124b40d30f2a10092d0318
|7=>0xa0c92d034c28324b40534c20a0c92d034c2830092d034c2a124b40d30828324b40534c2a624b40d31620a0c92d034c28324b42034cb8a0c92d034c3c40c92d034c60428324b40d30810324b40d30a70e
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x20606d415604140a6
|6,0=>0x14984c611983f70e583270b18266
|7,0=>0x641d89760617a75cdd6c759215c8555d4d851613d84d9d2e849a11e845dd10742210083e5cf183a9ce2836a0d2832a0c282ea0b372b1ca57276095823608671fa07681bdc6871820588
|8,0=>0xcc63298c863198c463098c062f89bbe6e69b7ded78b3a6c59af62b49aae6a38a6a6919a2628189e267089a22608962250891e63f88de230789e61f885a60d98161fc97ce5eb878e1db874a5ca870a1ba86c65a986825979
|9,0=>0x3bc9ed5fac9e9239c8e5238b9e0e37b8dce36b8d8e35a9d4a34a8d0a3399
|10,0=>0xf723d48f323c57
|11,0=>0x3e47
|_,_=>0
def wAt:=mkWire dB 50 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x24c4f3128d4a691008a3124d51413ce0a3524c4e3c28d493524c4e3560dca3924c402924d4a3128d401028c493124d4a254504f3828d49313ce0a2530d4a3524c4c35490440028c493534c522d1000a3124d514138f0a3524d49314904a350040a3124c49354504f382894c3528d4931
|1=>0x10dca31289493124a4a3138d493128c4f2534c4a353c9493128c4a3558cc93d28d483324d492928d4e2928d493110d4a3124d4c3520d4929280493528d4831289493558cc83524a4a3134c493e28d4a2530d4a3524c4d311000a3124d5f353ce8a3524c5633280493560dc8312894335
|2=>0x24c493528d4a313c94c3528d493158cca0124d43453ce0a3524c4a352454a2530d4a253ce0a3524c433560dc83134c483120d4a253cc4a3524d493174cca5d38d493128e4a3538d49310cc56332804a2528c433524c583720d483128958372444a3174dc8152894c3548b440028c4935
|3=>0x24d5633280493558cca0124d6b2900cc93534c4a3128d493d3cc4a35004893528c4f3128d4e2924c4a3530d491228c493110d4a31280493510d493528c48152894d31a4d491228c49110cd4a3124d4a3a24c493520cca2528c49290cd4e2924c49350c54a2534c4831289493538f8a35
|4=>0xcc493520c4a250cd48352894c3558cc835289493124a4a3128c4e3724c483120d4a2500a4d3124d4a3124a4d312054a2534c58372444a315cac03124d4a3538d493124a443528c49152894d3138dca2524c4a5d00c493520c4a250cd493528d4a3120d4a2530d4a2528d49311000a31
|5=>0xd3128949350cc4a2534c431534c4835289493e28d48372894a3128d491128c492928c433524c4a250cd4f3128d4a0124d4a3124d4c3528c4f3328d4a3124c403124d48172894d3130d4a3524c6e3120dca2500a493524c493e0cc4a350cc48372894a35
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x33000000c000
|6,0=>0x12a881436a0000b2800022a0c5
|7,0=>0x1788b845a9ac515a8a94531a8913c89a44b224cd1e88b4441a1110087c43c21d10e086d334a198cc666032f11690ae653427a12d08e844300010107a63941aa0c505a82a3
|8,0=>0x2a074d3a51d1ce8874139f1cece707353991cbce587293931c8ce4071d38d1c5ce287113871c2ce107053811bfcdf86f937b1bccde06ed37593a0dca6e23701374db46d736a1b44d9c6cb3641b14d846c02
|9,0=>0x1732b895bcada56b2b4959caca5632b0957caba55b2ac955caaa5532
|10,0=>0xbc0ddc6ec3751
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x13ac04c00110803fd00fc003ed00dfc037d00dbc036d00db0036500d00030c00c04029000a00022c0083402000073c0160001f4006e00104004000084000e000200007000040000
|1=>0x5dbc176d05cf413ff04ff413f004fb413d204e74136f04db412f004afc1282049bc1210048000f6d032440bef02fb40b7d028fc09ef025c8090001ff407ef01fb4077d01dbc076d
|2=>0xa0db5936d27db4936d22db483ed20da4636d18800604218100600112dfc436d1000427ef09f0825e209100226007db41f6007d001f20075801bed06db4196006400188f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x600200
|6,0=>0x1248580100010e
|7,0=>0x16b360454b90c4cf871418b014d48a3d4ee9baf6304eb219207a880642900034f052a72790
|8,0=>0x1aac6aeec5a391dc1b92ac9b47f521504f368c3976d2bc8861d163092520a7150ccab3ab208aa9b3e8d5e306
|9,0=>0x36aeecd354725f59b939da24269751
|10,0=>0x2ed4c5d
|11,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 18 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_61 7 roots_61 ops++addP pm 2 dom_237 10 roots_237 ops++addP pm 3 dom_249 10 roots_249 ops++addP pm 4 dom_181 6 roots_181 ops++addP pm 5 dom_221 9 roots_221 ops++addP pm 6 dom_245 9 roots_245 ops++addP pm 7 dom_157 6 roots_157 ops++addP pm 8 dom_189 9 roots_189 ops++addP pm 9 dom_125 9 roots_125 ops++addP pm 10 dom_93 6 roots_93 ops++addP pm 11 dom_117 6 roots_117 ops++addP pm 12 dom_213 6 roots_213 ops++addP pm 13 dom_29 4 roots_29 ops++addP pm 14 dom_53 4 roots_53 ops++addP pm 15 dzo_237_16 9 roots_237 ops++addP pm 16 dom_173 8 roots_173 ops++addP pm 17 dom_109 8 roots_109 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_237_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_109 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 42 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 50 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 17 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,34),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,18),(16,20),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,96),(64,192),(66,70),(66,74),(66,82),(66,98),(66,194),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,132),(128,136),(128,160),(128,192),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_126 10 roots_126 ops++addP pm 2 dom_250 10 roots_250 ops++addP pm 3 dom_246 10 roots_246 ops++addP pm 4 dom_238 10 roots_238 ops++addP pm 5 dom_222 10 roots_222 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_222 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
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
def isoMvS_247:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_223
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000fffe0000fffe0000fefe0000
def gsh_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000fffe0000fffe0000fefe
theorem lowS_zo_239_16_232:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_232)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,96),(64,192),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,129),(128,130),(128,132),(128,136),(128,160),(128,192),(144,145),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>3
|8=>9
|9=>26
|10=>36
|11=>16
|12=>3
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x929195ed820b9b6
|8,0=>0xd895ca66bb92be4748de6bcc0519f94216f33857314bd
|9,0=>0xef104ec06ae14e7c62e19404088a1f858f18585b77cd470d0a5c6d7536505148b505b64fc22475263f5e03c6532faf4244d31e8780fac40c7be08c6207177041ea
|10,0=>0xfa143d89e7cc8dec7aa2b9753abb36a763da69359fd2b9c83099cc07cde07cc3d78aa26f1d46c9816a58f605505e68f5c33f520dd4d3534497731ae22c8232bfee23ed61dc9f19c74186f114eea100820f28f0ae81060430316e
|11,0=>0xe469ad9c46d0692c7aa2c6a49bca8aa763d958018473d616d65853e445df430f134bde2bfee1b67e
|12,0=>0xfff0bd0b230eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffffffffffffffffff00ffff0000ffff0000ffffffffff00ff000000000000000000ffffffffff00ff000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffff00ff000000000000000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00000000000000000000000000000000000000000000ff00ffffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
|0,1=>0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ffffffff00000000ff00ff00ff00ff00ffffffff00000000ffffffff00ff00ffffffffff00000000ffffffff00ff00ffffffffff00000000fffffffffff0fff0f0f0f0f0f0f0f0f0fffffffffff0fff0f0f0f0f0f0f0f0f0ffffffffffffff00ffff0000ffff0000ffffffffffffff00ffff0000ffff0000ffffffffffccffccccccccccccccccccffffffffffccffcccccccccccccccccc0000000000ff00ffff00ff00ff00ff000000000000ff00ffff00ff00ff00ff000000000000ff00ffffffffff000000000000000000ff00ffffffffff000000000000000000ff00ff00000000000000000000000000ff00ff0000000000000000ffffffffffaaffaaaaaaaaaaaaaaaaaaffffffffffaaffaaaaaaaaaaaaaaaaaaffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff000000000000ff00ffffffffffff00ff000000000000ff00ffffffffffff00ff000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8168812a20825169e7020c41045a7a28831040d3a9e31040883c620810c291220816732883104089904104a2d3948310408641e3104083cc82082516b2044882041cca78c4101ca448820398a418820
|1=>0x1040b41d4418b406a9e31040b41e64188208b6041882043144ae441034e4104128adac9c0820824d860831040d9c083104116d144188206b204188366b082082515b66a2082093593812a2081ac53c62
|2=>0x1040b6b1441f0205b4ec20c410456d51062d016d3cd44188206ab631040b6b20418820734ea2082092dac81062081076104104a2b6b20418b4069d44188366c083106cd208209456d3a8831040861483
|3=>0x1040b6b204104125b604188207359d20c4102daa20c41b2db020c410456d9c144188205b584188208ada79a895188206c095188208b5902544102da7510620816d3c083104115b544188205a0f382883
|4=>0x188365b593810620816d640951040d3b144188205b58a20c4102d0c51062d016d9a8831040b6b15b188205b66a20c4105da751062081cd82bc4188206cd44a8c41035441f0205b59381062081a79a883
|5=>0x734ec510620816d510620822b6a8831040bbb66a20c4102dac810620816d82883104125b4ea254620816d628831040bbb60a254620816d64d44188205b544188205b9a7510620816d828831041f6b144
|6=>0xa20c4102dac510620816d510620817f6c144188205b60a25462081bd510620816d628831040b
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xf8021c008
|8,0=>0x588145c49810243880c2028807e4178
|9,0=>0x4d612ba48e11b8451d0c84120fb93ce0eb838a4db734a4c993024b882be4a7827e096923a08591f247391a68609
|10,0=>0x9ea670a9a225ea95664c990e63a98c6628987e616983a20597ee9f297aa1e197661d0971a9bd96ce9aa9686598963a98685eed7295a2960855e54f851a53d9
|11,0=>0xc467089bfaaf4abae6e29b666d09b1aabcaacaaa8aa7aa959a326839
|12,0=>0x32c9c8e71a9
|13,0=>0x3358
|_,_=>0
def wAt:=mkWire dB 32 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3af80d52d3bb62d62c50d22162d73562c50d52d22173562c1a91a152173562c1a93a362d73562c50d80f3ab3af80d52d52162d73562c1a922173552d62c1a962f38f3ab62d1a91a173552d62c1a93a322162d73562c1a152162d73562c1a93a3
|1=>0xb962c50d22173562c50d5563afaa91ad52d73562c1a9abb1ad62c50d80f3ab80d52d62f50d80f52d83b52d62c1a93ab3af80d52d9dd62e62f50d03952d62c1a938f3ab62d1a91c23af80d52d1ad52d62f1a922173562c50d80f52daab1ad3ab
|2=>0x50d3ab80d52d73562c50d3af80d52d13962c50d3ab62d1a90b962c50d62d62f50d23962c50d52d62c1a980d80f52d73552d62c1a938f3ab62d1a90b952d62c1a962d03962c50d52d03962c1a93ab80d80f52d62d73562c50d52173562c1a962d
|3=>0x62c50d0b962c50d63b62c50d23962c50d62e62f50d62d62c50d87f52d1ae3afaa91ad13962c50d52d62f1a962d62f50d50d80f52d52d62c1a955d62e1a903962c50d52daab1ad3af80d52d3ab62d1a93afaa91ad52daab1ad1ad52d1a99ad62f
|4=>0x50d1ae52d1ad52d57d1ae62c50d62d50daab1ad62e50d62f50d52d1a980f52daa91ad62e50d1ad52d62f50d62c50d62d50d52d1ae03962c50d52d62f1a950d1ad52d9ad62f50d735
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x1d402c001
|8,0=>0x34517a8a944aa2050da859422a0c5
|9,0=>0x13a89944aa24511a889442a2050fa87943aa1c50da869432a1850ba85942aa14509a849422a10507a8394
|10,0=>0x851c1ce0870137f1becdf06f53791bbcdd86e93731b8cdc06dd36d1b5cda86d13671b2cd906c53611afcd786b935b1accd606ad3551a9cd486a13
|11,0=>0x9594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2
|12,0=>0x4bc65c32d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 13
def pmP:Nat→Nat
|0=>0x7bbf07b9f0529f04f9f04adf04abf04a9f0489f042ff042df042bf0429f0406c033b700fbf008450077f003ff002ff002d3002bf002b70029f00297002130007f0007c0002d00020000040000100000
|1=>0x8429f44a9f442bf402ff3ca9f382ff1c2bf0c29f08297
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x2183
|8,0=>0xe4981473df051
|9,0=>0x6909a380935c95420a24c5082c989b25478910d
|10,0=>0x91551766765d65751651435551984b55b59450d3544e86d425468b
|11,0=>0x514659254254556657654254
|12,0=>0x9514
|13,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_247 11 roots_247 ops++addP pm 3 dom_223 11 roots_223 ops++addP pm 4 dom_127 12 roots_127 ops++addP pm 5 dom_159 7 roots_159 ops++addP pm 6 dom_183 7 roots_183 ops++addP pm 7 dom_251 12 roots_251 ops++addP pm 8 dom_63 8 roots_63 ops++addP pm 9 dom_239 12 roots_239 ops++addP pm 10 dom_95 9 roots_95 ops++addP pm 11 dom_215 7 roots_215 ops++addP pm 12 dzo_239_16 10 roots_239 ops++addP pm 13 dom_43 5 roots_43 ops++addP pm 14 dom_191 10 roots_191 ops++addP pm 15 dom_190 9 roots_190 ops++addP pm 16 dom_222 10 roots_222 ops++addP pm 17 dom_246 10 roots_246 ops++addP pm 18 dom_189 9 roots_189 ops++addP pm 19 dom_187 9 roots_187 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_239_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_187 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 9 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 26 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 26 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 36 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 16 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 16 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [7, 0] }, { op := GateOp.or, inputs := [4, 7] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [2, 8] }, { op := GateOp.or, inputs := [11, 9] }, { op := GateOp.or, inputs := [8, 7] }, { op := GateOp.or, inputs := [13, 2] }, { op := GateOp.and, inputs := [14, 11] }, { op := GateOp.and, inputs := [5, 3] }, { op := GateOp.and, inputs := [10, 12] }, { op := GateOp.and, inputs := [15, 6] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52668_aux

theorem PEqualNP.Outside.L_meta_52668 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52668_aux.main
