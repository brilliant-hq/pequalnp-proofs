import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18560

namespace PriorG11.SharedCases
abbrev Slice := Inhabited (Fin 4)

variable [sctx : Slice]

def choose {α : Type} (a b c d : α) : α :=
  match sctx.default.val with | 0 => a | 1 => b | 2 => c | _ => d

namespace Rup
abbrev qv:=Nat×Bool
abbrev q0:=List qv
def w3 (l:qv):qv:=(l.1,!l.2)
def w2 (v:Nat->Bool)(l:qv):Prop:=v l.1=l.2
def Holds (v:Nat->Bool)(c:q0):Prop:=∃l∈c,w2 v l
def ep0N (e:Nat):=[0,0,1,1,2,2,3,3,4,4,5,5,6,7].getD e 0
def ep1N (e:Nat):= choose ([3,7,4,9,5,6,7,9,7,8,6,9,8,8].getD e 0) ([8,9,4,9,5,6,7,9,7,8,6,9,8,8].getD e 0) ([8,9,3,7,5,6,7,9,7,8,6,9,8,8].getD e 0) ([8,9,3,7,4,9,7,9,7,8,6,9,8,8].getD e 0)
def epN (s e:Nat):=if s==0 then ep0N e else ep1N e
def neighN (x:Nat):= choose ([136,528,96,641,386,580,292,281,208,42].getD x 0) ([768,528,96,640,386,580,292,280,209,43].getD x 0) ([768,136,96,642,384,580,292,282,209,41].getD x 0) ([768,136,528,642,388,576,288,282,209,45].getD x 0)
def adjB (x y:Nat):=(neighN x).testBit y
def nbrsN (x:Nat):List Nat:= choose ([[3,7],[4,9],[5,6],[0,7,9],[1,7,8],[2,6,9],[2,5,8],[0,3,4,8],[4,6,7],[1,3,5]].getD x []) ([[8,9],[4,9],[5,6],[7,9],[1,7,8],[2,6,9],[2,5,8],[3,4,8],[0,4,6,7],[0,1,3,5]].getD x []) ([[8,9],[3,7],[5,6],[1,7,9],[7,8],[2,6,9],[2,5,8],[1,3,4,8],[0,4,6,7],[0,3,5]].getD x []) ([[8,9],[3,7],[4,9],[1,7,9],[2,7,8],[6,9],[5,8],[1,3,4,8],[0,4,6,7],[0,2,3,5]].getD x [])
def avoidMask (a:Nat):= choose ([28,49,56,67,74,88,134,162,194,263,270,291,298,533,593,773].getD a 0) ([15,29,43,57,75,89,135,163,195,270,298,532,592,644,704,772].getD a 0) ([23,29,51,57,83,89,133,161,193,268,290,296,534,594,644,774].getD a 0) ([39,45,51,57,71,77,83,89,165,197,294,300,594,704,770,770].getD a 0)
def qd (x y:Nat):Nat->Nat×Nat
 | 0=>(0,0)
 | i+1=>if ep0N i==x&&ep1N i==y then (i,0) else if ep1N i==x&&ep0N i==y then (i,1) else qd x y i
def edgeIdxS (x y:Nat):=qd x y 14
def inIB (I x:Nat):=I.testBit x
def capN (k I x:Nat):=if inIB I x then 1 else 2+k
def ineligNbrsN (I x:Nat):List Nat:=(nbrsN x).filter (inIB I)
def eligNbrsN (I x:Nat):List Nat:=(nbrsN x).filter (λ y=>!(inIB I y))
def pop3 (m:Nat):=(m&&&1)+((m>>>1)&&&1)+((m>>>2)&&&1)
def unsl (s:Nat):=(s / 5,s % 5)
def fLive (x j:Nat):Nat:=x*5+j
def fLab (x j c:Nat):Nat:=50+(x*5+j)*10+c
def fOpp (x j c:Nat):Nat:=550+(x*5+j)*10+c
def fRes (t x:Nat):Nat:=1050+t*10+x
def fCommon (x y:Nat):Nat:=1080+(min x y)*10+(max x y)
def fDiff (t x y:Nat):Nat:=1180+(t*10+x)*10+y
def fEqGe (t x:Nat):Nat:=1480+t*10+x
def fHm (x:Nat):Nat:=1500+x
def fRsub (t x j:Nat):Nat:=1510+(t*10+x)*5+j
def fEs (s e x:Nat):Nat:=1660+(s*14+e)*10+x
def fRa (s e x j:Nat):Nat:=1940+((s*14+e)*10+x)*5+j
def fFree (x j:Nat):Nat:=3340+x*5+j
def fEmpty (x j:Nat):Nat:=3390+x*5+j
def fGate (b a:Nat):Nat:=3440+b*14+a
def fGflip (b a:Nat):Nat:=3636+b*14+a
def fSgate (b a:Nat):Nat:=3832+(min b a)*14+(max b a)
def fLt (b a:Nat):Nat:=4028+b*14+a
def fAfter (e x j:Nat):Nat:=4224+(e*10+x)*5+j
def fHsec (e:Nat):Nat:=4924+e
def fSecp (e b a:Nat):Nat:=4938+(e*5+b)*5+a
def fAfree (e x j:Nat):Nat:=5288+(e*10+x)*5+j
def fAempty (e x j:Nat):Nat:=5988+(e*10+x)*5+j
def fStay (e:Nat):Nat:=6688+e
def fPick (e z:Nat):Nat:=6716+e*10+z
def fH0 (e z l:Nat):Nat:=6856+(e*10+z)*5+l
def fBc (a b:Nat):Nat:=7742+a*14+b
def fAvoid (x a j:Nat):Nat:=7998+(x*16+a)*5+j
def fEfh (a l:Nat):Nat:=8798+a*5+l
def fEse (a b:Nat):Nat:=9118+a*14+b
def fMesc (a z l:Nat):Nat:=10014+(a*10+z)*5+l
def fSmate (x j y l:Nat):Nat:=11230+((x*5+j)*10+y)*5+l
def fOmate (x j y l:Nat):Nat:=13730+((x*5+j)*10+y)*5+l
def fIfilt (i y a l:Nat):Nat:=16230+((i*10+y)*3+a)*5+l
def maskRes (k a x:Nat):q0:=(if 0<k&&a.testBit 0 then [(fRes 0 x,true)] else [])++(if 1<k&&a.testBit 1 then [(fRes 1 x,true)] else [])++(if 2<k&&a.testBit 2 then [(fRes 2 x,true)] else [])
def uvSlots (k I u v a b:Nat)(f:Nat->Nat->qv):q0:=(if u != a&&u != b then (List.range (capN k I u)).map (f u) else [])++(if v != a&&v != b then (List.range (capN k I v)).map (f v) else [])
def untriple (b:List Nat)(a:Nat):=let v:=b.getD a 0;(v&&&15,(v>>>4)&&&15,(v>>>8)&&&15)
abbrev unctx:=untriple
def validTriple (b:List Nat)(a:Nat):=a<b.length&&let t:=untriple b a;t.1<14&&t.2.1<10&&t.2.2<10&&!adjB t.2.1 t.2.2
def validCtx (d b:List Nat)(a:Nat):=a<b.length&&let c:=unctx b a;validTriple d c.1&&c.2.1<14&&c.2.2<10
def unmask (b:List Nat)(a:Nat):=let v:=b.getD a 0;(v&&&15,(v>>>4)&&&16383,(v>>>18)&&&1023)
def validMask (b:List Nat)(a:Nat):=a<b.length&&a<6&&let u:=unmask b a;u.1<14&&u.2.1.testBit u.1
namespace R1
abbrev P (x:Nat):qv:=(x,true)
abbrev M (x:Nat):qv:=(x,false)
abbrev G (k I:Nat)(s:Nat×Nat):Bool:=s.1<10&&s.2<capN k I s.1
abbrev C a b:=[M a,P b]
abbrev W a b:=[M a,M b]
abbrev K a b c:=[M a,M b,P c]
abbrev p2 a b c:=[M a,P b,P c]
abbrev L:=unsl
abbrev N:=List.range
abbrev B:=inIB
abbrev D:=capN
abbrev F:=fLive
abbrev E:=fOpp
abbrev O:=untriple
abbrev R:=fLab
abbrev S:=fRes
abbrev V:=ineligNbrsN
abbrev U:=ep1N
abbrev A:=ep0N
abbrev H:=fSgate
abbrev Q:=fRa
abbrev T:=unctx
abbrev X:=nbrsN
abbrev J:=fEs
abbrev z3:=fAfter
abbrev z4:=validTriple
abbrev z5:=fCommon
abbrev z6:=fAempty
abbrev z9:=uvSlots
abbrev za:=fPick
abbrev zb:=fHsec
abbrev zc:=validCtx
abbrev zd:=fSecp
abbrev ze:=fIfilt
abbrev zf:=fFree
abbrev zg:=eligNbrsN
abbrev zh:=avoidMask
end R1
section B0
open R1
def expand0 (k I g r:Nat):q0:=let c n m:=(r>>>n)&&&m;let e:=L (r&&&63);let f:=e.1;let h:=e.2;let i:=L (c 6 63);let m:=i.1;let n:=i.2;let o:=L (c 3 63);let p:=o.1;let q:=o.2;let s:=D k I;let u:=r&&&15;let v:=r&&&7;let w:=c 6 15;let z:=c 4 15;let Y:=c 3 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<16 then a 4 8 12 (a 1 2 3 [P (F u 0)] (C (F f h) (R f h f)) (C (F f (h+1)) (F f h)) (K (F f h) (R f h w) (z5 f w))) (a 5 6 7 (M (F u (2+(c 4 7)))::maskRes k (c 7 7) u) [M (S z u)] [M (z5 u z)] (K (S v Y) (S v (c 7 15)) (z5 Y (c 7 15)))) (if g<10 then let y:=c 7 15;if g<9 then [M (fDiff v Y y),P (S v Y)] else [M (fDiff v Y y),M (S v y)] else if g<11 then [P (z5 z (c 8 15))] else [M (z5 u z),M (F u (c 11 7)),P (R u (c 8 7) z),P (R u (c 11 7) z)]++(N k).map (λ t=>P (fDiff t u z))) (a 13 14 15 ((N (s u)).map (λ j=>P (fAvoid u z j))) (C (fAvoid f w h) (F f h)) (W (fAvoid f w h) (R f h (c 10 15))) (C (S u 9) (S (u+1) 9))) else a 20 24 28 (a 17 18 19 (let b:=(c 4 1)==1;[(S u 9,b),(S (u+1) 9,b),P (fEqGe u 9)]) (K (fEqGe v (Y+1)) (S v Y) (S (v+1) Y)) (let b:=(c 7 1)==1;[M (fEqGe v (Y+1)),(S v Y,b),(S (v+1) Y,b),P (fEqGe v Y)]) [M (fHm u)]) (a 21 22 23 (W (fHm u) (F u (1+k))) (M (fHm u)::M (F u (1+(c 4 7)))::maskRes k (c 7 7) u) (C (fRsub v p q) (F p q)) (K (fRsub v p q) (S v (c 9 15)) (R p q (c 9 15)))) (a 25 26 27 (M (S v p)::P (fHm p)::((N (s p)).filter (λ j=>j != q)).map (λ j=>P (fRsub v p j))) [M (E f h f)] [M (F f h),M (R f h w),M (E f h w),P (fHm w)] (M (F f h)::M (R f h w)::P (E f h w)::(N (s w)).map (λ l=>P (fSmate f h w l)))) (a 29 30 31 (C (fSmate f h m n) (F m n)) (let d:=c 12 15;let b:=(c 17 1)==1;[M (fSmate f h m n),((if ((c 16 1)==1) then E m n d else R m n d),b),((if ((c 16 1)==1) then E f h d else R f h d),!b)]) (M (F f h)::M (E f h w)::P (R f h w)::(N (s w)).map (λ l=>P (fOmate f h w l))) (C (fOmate f h m n) (F m n)))
def expand1 (k I g r:Nat):q0:=let f n m:=(r>>>n)&&&m;let h:=L (r&&&63);let m:=h.1;let n:=h.2;let o:=L (f 6 63);let p:=o.1;let t:=o.2;let u:=L (f 5 63);let v:=u.1;let w:=u.2;let z:=r&&&15;let Y:=f 4 15;let Z:=f 1 15;let c a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<48 then c 36 40 44 (c 33 34 35 (let d:=f 12 15;let b:=(f 17 1)==1;[M (fOmate m n p t),((if ((f 16 1)==1) then E p t d else R p t d),b),((if ((f 16 1)==1) then R m n d else E m n d),!b)]) [M (F m n),M (E m n (f 6 15)),M (zf m n)] [M (F m n),M (E m n (f 6 15)),M (E m n (f 10 15))] (let d:=f 10 15;let b:=(f 14 1)==1;[M (F m n),M (E m n (f 6 15)),(R m n d,b),(E (f 6 15) 0 d,!b)])) (c 37 38 39 [M (F z (f 8 7)),M (F z (f 11 7)),M (E z (f 8 7) Y),M (E z (f 11 7) Y)] [P (E z 0 Y)] (M (E z 0 Y)::(N (D k I ((X z).getD (f 8 3) 0))).map (λ l=>P (ze z Y (f 8 3) l))) [M (E z 0 Y)]) (c 41 42 43 [M (J (f 4 1) z (epN (1-(f 4 1)) z))] (K (J 0 z Y) (J 1 z Y) (fHm Y)) [P (J (f 4 1) z (epN (f 4 1) z))] (let s:=r&&&1;let x:=f 5 15;M (J s Z x)::P (J (1-s) Z x)::(N (D k I x)).map (λ j=>P (Q s Z x j)))) (c 45 46 47 (W (Q (r&&&1) Z (f 5 15) (f 9 7)) (Q (r&&&1) Z (f 5 15) (f 12 7))) (C (Q (r&&&1) Z v w) (F v w)) (C (Q (r&&&1) Z v w) (J (r&&&1) Z v)) (W (Q (r&&&1) Z v w) (J (1-(r&&&1)) Z v))) else c 52 56 60 (c 49 50 51 (let s:=r&&&1;let y:=f 11 15;let b:=(f 16 1)==1;[M (Q s Z v w),((if ((f 15 1)==1) then E v w y else R v w y),b),((J (if ((f 15 1)==1) then 1-s else s) Z y),!b)]) [P (F m n)] [P (E m n (f 6 15))] (let a:=edgeIdxS m ((V I m).getD n 0);[P (Q a.2 a.1 m n)])) (c 53 54 55 (let a:=edgeIdxS z ((zg I z).getD 0 0);[P (Q a.2 a.1 z (V I z).length)]) (let e:=f 13 15;K (fSmate m n p t) (Q (f 12 1) e p t) (Q (f 12 1) e m n)) (let e:=f 13 15;K (fOmate m n p t) (Q (f 12 1) e p t) (Q (1-(f 12 1)) e m n)) (C (zf m n) (F m n))) (c 57 58 59 (W (zf m n) (Q (f 6 1) (f 7 15) m n)) (C (fEmpty m n) (F m n)) (W (fEmpty m n) (E m n (f 6 15))) (C (fGate z Y) (H z Y))) (if g<62 then if g<61 then [M (fGflip z Y),P (H z Y)] else [M (H z Y),P (fGate z Y),P (fGflip z Y)] else if g<63 then let q:=L (f 8 63);[M (Q (f 14 1) z q.1 q.2),M (Q (f 15 1) Y q.1 q.2),((if (f 14 1)==(f 15 1) then fGate z Y else fGflip z Y),true)] else let b:=(f 13 1)==1;[M (fGate z Y),(J (f 8 1) z (f 9 15),b),(J (f 8 1) Y (f 9 15),!b)])
def expand2 (k I _m g r:Nat):q0:=let c n m:=(r>>>n)&&&m;let d:=L (c 4 63);let f:=d.1;let h:=d.2;let i:=r&&&15;let j:=c 4 15;let n:=c 4 31;let o:=L n;let q:=o.1;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<80 then a 68 72 76 (a 65 66 67 (let b:=(c 13 1)==1;[M (fGflip i j),(J (c 8 1) i (c 9 15),b),(J (1-(c 8 1)) j (c 9 15),!b)]) (W (H i j) (fLt i j)) [P (H i j),P (fLt i j),P (fLt j i)] (W (fLt i j) (fLt j i))) (a 69 70 71 (K (fLt i j) (fLt j (c 8 15)) (fLt i (c 8 15))) (C (z3 i f h) (F f h)) (W (z3 i f h) (Q (c 10 1) i f h)) (K (z3 i f h) (Q (c 10 1) (c 11 15) f h) (fLt i (c 11 15)))) (if g<74 then if g<73 then [M (fAfree i f h),P (z3 i f h)] else [M (fAfree i f h),P (zf f h)] else if g<75 then [M (z6 i f h),P (z3 i f h)] else [M (z6 i f h),P (fEmpty f h)]) (if g<78 then if g<77 then [M (zd i q o.2),P (F (A i) q)] else [M (zd i q o.2),P (F (U i) o.2)] else if g<79 then W (zd i q o.2) (Q 0 i (A i) q) else W (zd i q o.2) (Q 1 i (U i) o.2)) else a 84 88 92 (a 81 82 83 (let y:=c 9 15;let b:=(c 14 1)==1;[M (zd i q o.2),((if ((c 13 1)==1) then R (U i) o.2 y else R (A i) q y),b),((if ((c 13 1)==1) then E (A i) q y else E (U i) o.2 y),!b)]) (M (zb i)::(N (D k I (A i))).flatMap λ b=>(N (D k I (U i))).map λ e=>P (zd i b e)) (P (fStay i)::(N 10).map (λ z=>P (za i z))) []) (if g<86 then if g<85 then [M (H i j),M (fStay i),P (fStay j)] else let z:=c 8 15;[M (H i j),M (za i z),P (za j z)] else if g<87 then C (fH0 i f h) (z3 i f h) else p2 (fH0 i f h) (E f h (A i)) (E f h (U i))) (a 89 90 91 (M (za i j)::P (zb i)::(N (D k I j)).map (λ l=>P (fH0 i j l))) [] [] (let s:=L (r&&&63);C (E s.1 s.2 (c 6 15)) (F s.1 s.2))) []
def expand3 (k I:Nat)(t0 c0 x1:List Nat)(g r:Nat):q0:=let f n m:=(r>>>n)&&&m;let h:=D k I;let m:=z9 k I;let n:=O t0;let o:=T c0;let q:=r&&&15;let u:=r&&&63;let v:=f 4 15;let w:=f 6 15;let Y:=f 6 7;let Z:=f 8 3;let d a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<112 then d 100 104 108 (d 97 98 99 [] (let a:=(f 4 1)==1;let t:=n q;K (J 0 t.1 (if a then t.2.2 else t.2.1)) (J 1 t.1 (if a then t.2.1 else t.2.2)) (fBc q t.1)) (let t:=n q;[M (fBc q v),M (fStay v),P (zb t.1)]++m (A t.1) (U t.1) t.2.1 t.2.2 (λ z l=>P (z6 v z l))) []) (d 101 102 103 [] (let c:=o u;let a:=c.2.1;let b:=c.2.2;let t:=n c.1;[M (fBc c.1 a),M (za a b)]++m (A t.1) (U t.1) t.2.1 t.2.2 (λ z l=>P (z6 a z l))++[P (zb t.1)]++(if b != t.2.1&&b != t.2.2 then [P (fHm b)] else [])++(N (h b)).flatMap (λ l=>[P (fEfh u l),P (fAfree a b l)])++((N 14).filter (λ e=>e != a)).map (λ e=>P (fEse u e))) (C (fEfh u Y) (z3 (o u).2.1 (o u).2.2 Y)) (let t:=n (o u).1;W (fEfh u Y) (E (o u).2.2 Y (if ((f 9 1)==1) then t.2.2 else t.2.1)))) (d 105 106 107 (let c:=o u;p2 (fEfh u Y) (E c.2.2 Y (A (n c.1).1)) (E c.2.2 Y (U (n c.1).1))) (C (fEse u w) (fLt (o u).2.1 w)) (p2 (fEse u w) (J 0 w (o u).2.2) (J 1 w (o u).2.2)) (C (fEse u w) (fBc (o u).1 w))) (d 109 110 111 (let a:=r&&&7;let um:=unmask x1 a;let am:=um.2.1;let cm:=um.2.2;P (zb um.1)::((N 14).filter (λ e=>am.testBit e)).flatMap (λ e=>P (fStay e)::((N 10).filter (λ z=>!(cm.testBit z))).map (λ z=>P (za e z)))++((N 10).filter (λ z=>cm.testBit z)).flatMap (λ z=>(N (h z)).flatMap (λ l=>P (zf z l)::P (fMesc a z l)::((N 10).filter (λ y=>cm.testBit y)).map (λ y=>P (E z l y))))) (let a:=r&&&7;let d:=(unmask x1 a).1;let s:=L (f 3 63);p2 (fMesc a s.1 s.2) (E s.1 s.2 (A d)) (E s.1 s.2 (U d))) (let a:=r&&&7;let am:=(unmask x1 a).2.1;let s:=L (f 3 63);M (fMesc a s.1 s.2)::((N 14).filter (λ e=>!(am.testBit e))).flatMap (λ e=>[P (Q 0 e s.1 s.2),P (Q 1 e s.1 s.2)])) []) else d 116 120 124 [] (d 117 118 119 [] (let x0:=(X q).getD Z 0;C (ze q v Z (f 10 7)) (z6 (edgeIdxS q x0).1 x0 (f 10 7))) (C (ze q v Z (f 10 7)) (zf ((X q).getD Z 0) (f 10 7))) (W (ze q v Z (f 10 7)) (R ((X q).getD Z 0) (f 10 7) v))) (d 121 122 123 (C (ze q v Z (f 10 7)) (R ((X q).getD Z 0) (f 10 7) (f 13 15))) [] (W (za q v) (za q (f 8 15))) []) (d 125 126 127 [] (let s:=L u;C (R s.1 s.2 w) (F s.1 s.2)) (M (z5 q v)::(N (h q)).map (λ j=>P (R q j v))++(N (h v)).map (λ l=>P (R v l q))) (let p:=f 4 3;let a:=if p==2 then 1 else 0;let b:=if p==0 then 1 else 2;let y1:=f 6 15;let y2:=f 10 15;let j:=f 14 7;[P (fHm q),M (S a q),M (S b q),M (S a y1),P (S b y1),M (S b y2),P (S a y2),M (F q j),P (fRsub a q j),P (fRsub b q j)]++(if 2<k then [P (F q 4)] else [])))
def expandScheme (k I b:Nat)(c d e:List Nat)(a:Nat):q0:=let f:=a&&&127;let r:=a>>>7;if f<64 then if f<32 then expand0 k I f r else expand1 k I f r else if f<96 then expand2 k I b f r else expand3 k I c d e f r
def enabled0 (k I g r:Nat):Bool:=let e n m:=(r>>>n)&&&m;let f:=L (r&&&63);let h:=f.1;let m:=L (e 6 63);let n:=m.1;let o:=L (e 3 63);let p:=o.1;let q:=D k I;let s:=G k I;let u:=B I;let v:=r&&&15;let w:=r&&&7;let z:=e 6 15;let N:=e 4 15;let Y:=e 3 15;let c a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<16 then c 4 8 12 (c 1 2 3 (v<10) (s f) (h<10&&f.2+1 < q h) (s f&&z<10)) (c 5 6 7 (v<10&&!u v&&(e 4 7) < k&&(e 7 7)<(1<<<k)&&pop3 (e 7 7)==k-(e 4 7)) (v<10&&u v&&N < k) (v < N&&N<10&&(u v||u N)) (w < k&&Y < (e 7 15)&&(e 7 15)<10)) (if g<10 then w < k&&Y<10&&(e 7 15)<10&&Y != (e 7 15) else if g<11 then let b:=e 8 15;v<10&&u v&&N<10&&b<10&&N != b&&adjB v N&&adjB v b else v<10&&!u v&&N<10&&N != v&&(e 8 7) < (e 11 7)&&(e 11 7) < q v) (c 13 14 15 (v<10&&N<16&&!((zh N).testBit v)&&((zh N)&&&neighN v) != 0) (s f&&z<16) (let y:=e 10 15;s f&&z<16&&y<10&&(zh z).testBit y) (v+1 < k)) else c 20 24 28 (c 17 18 19 (v+1 < k) (w+1 < k&&Y<9) (w+1 < k&&0 < Y&&Y<9) (v<10&&u v)) (c 21 22 23 (v<10&&!u v) (v<10&&!u v&&(e 4 7) < k&&(e 7 7)<(1<<<k)&&pop3 (e 7 7)==k-(e 4 7)) (w < k&&p<10&&!u p&&o.2 < q p) (w < k&&p<10&&!u p&&o.2 < q p&&(e 9 15)<10)) (c 25 26 27 (w < k&&p<10&&!u p&&o.2 < q p) (s f) (s f&&z<10&&z != h) (s f&&z<10&&z != h&&!u z)) (if g<30 then let a:=s f&&n<10&&n != h&&!u n&&m.2 < q n;if g<29 then a else a&&(e 12 15)<10 else if g<31 then s f&&z<10&&z != h&&!u z else s f&&n<10&&n != h&&!u n&&m.2 < q n)
def enabled1 (k I m g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=L (r&&&63);let f:=c.1;let h:=c.2;let l:=L (b 6 63);let n:=l.1;let o:=L (b 5 63);let p:=D k I;let s:=G k I;let t:=B I;let u:=r&&&15;let v:=b 4 15;let w:=b 6 15;let z:=b 1 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<48 then a 36 40 44 (a 33 34 35 (s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 12 15)<10) (s c&&w<10&&w != f&&t w) (let d:=b 10 15;s c&&w<10&&w != f&&t w&&d<10&&d != w) (s c&&w<10&&w != f&&t w&&(b 10 15)<10)) (a 37 38 39 (u<10&&!t u&&v<10&&t v&&(b 8 7) < (b 11 7)&&(b 11 7) < p u) (u<10&&t u&&v<10&&adjB u v) (m==1&&u<10&&t u&&v<10&&!t v&&!adjB u v&&(b 8 3)<3&&(b 8 3)<(X u).length) (u<10&&t u&&v<10&&t v&&u != v)) (a 41 42 43 (u<14) (u<14&&v<10) (u<14) (z<14&&(b 5 15)<10)) (if g<46 then if g<45 then z<14&&(b 5 15)<10&&(b 9 7) < (b 12 7)&&(b 12 7) < p (b 5 15) else z<14&&s o else z<14&&s o) else a 52 56 60 (a 49 50 51 (z<14&&s o&&(b 11 15)<10) (f<10&&!t f&&h < ((V I f).length+(if (zg I f).isEmpty then 0 else 1))&&h < p f) (f<10&&!t f&&h < (V I f).length&&h < p f&&(V I f).getD h 10==w) (f<10&&!t f&&h<(V I f).length&&h < p f)) (a 53 54 55 (u<10&&!t u&&!(zg I u).isEmpty&&(V I u).length < p u) (s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 13 15)<14) (s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 13 15)<14) (s c)) (a 57 58 59 (s c&&(b 7 15)<14) (s c) (s c&&w<10) (u < v&&v<14)) (if g<62 then u < v&&v<14 else if g<63 then u < v&&v<14&&s (L (b 8 63)) else u < v&&v<14&&(b 9 15)<10)
def enabled2 (k I m g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=L (b 4 63);let d:=D k I;let f:=G k I;let h:=r&&&15;let i:=b 4 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<80 then a 68 72 76 (if g<66 then if g<65 then h < i&&i<14&&(b 9 15)<10 else h<14&&i<14&&h != i else h < i&&i<14) (a 69 70 71 (let e:=b 8 15;h<14&&i<14&&e<14&&h != i&&i != e&&h != e) (h<14&&f c) (h<14&&f c) (h<14&&f c&&(b 11 15)<14&&(b 11 15) != h)) (h<14&&f c) (let p:=L (b 4 31);h<14&&p.1 < d (A h)&&p.2 < d (U h)) else a 84 88 92 (a 81 82 83 (let p:=L (b 4 31);h<14&&p.1 < d (A h)&&p.2 < d (U h)&&(b 9 15)<10) (h<14) (m>0&&h<14) false) (if g<86 then let e:=m>0&&h<14&&i<14&&h != i;if g<85 then e else e&&(b 8 15)<10 else m>0&&h<14&&f c) (a 89 90 91 (m>0&&h<14&&i<10) false false (f (L (r&&&63))&&(b 6 15)<10)) false
def enabled3 (k I m _q:Nat)(t0 c0 x0:List Nat)(g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=D k I;let d:=B I;let e:=zc t0 c0;let h:=z4 t0;let j:=r&&&15;let n:=b 4 15;let o:=r&&&63;let p:=b 6 7;let u:=b 6 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;a 104 112 120 (if g<100 then a 97 98 99 false (m>0&&h j) (m>0&&h j&&n<14) false else if g<102 then if g<101 then false else m>0&&e o else m>0&&e o&&p < c (T c0 o).2.2) (a 105 108 110 (m>0&&e o&&p < c (T c0 o).2.2) (m>0&&e o&&u<14&&u != (T c0 o).2.1) (if g<109 then m==1&&validMask x0 (r&&&7) else m==1&&validMask x0 (r&&&7)&&G k I (L (b 3 63))) (if g<111 then m==1&&validMask x0 (r&&&7)&&G k I (L (b 3 63)) else false)) (a 115 116 117 false false false (m==1&&j<10&&d j&&n<10&&!d n&&!adjB j n&&(b 8 3)<3&&(b 8 3)<(X j).length&&(b 10 7) < c ((X j).getD (b 8 3) 0))) (if g<124 then a 121 122 123 (m==1&&j<10&&d j&&n<10&&!d n&&!adjB j n&&(b 8 3)<3&&(b 8 3)<(X j).length&&(b 10 7) < c ((X j).getD (b 8 3) 0)&&(b 13 15)<10&&adjB j (b 13 15)) false (m>0&&j<14&&n < (b 8 15)&&(b 8 15)<10) false else a 125 126 127 false (G k I (L o)&&u<10) (j < n&&n<10&&!d j&&!d n) (j<10&&!d j&&let p:=b 4 3;((p==0&&1<k)||(0<p&&p<3&&2<k))&&(b 6 15)<10&&(b 10 15)<10&&(b 14 7)<c j))
end B0
def enabled (k I a c:Nat)(d e f:List Nat)(b:Nat):Bool:=let g:=b&&&127;let r:=b>>>7;if g<64 then if g<32 then enabled0 k I g r else enabled1 k I a g r else if g<96 then enabled2 k I a g r else enabled3 k I a c d e f g r
abbrev expS:=expandScheme
abbrev enS:=enabled
end Rup

end PriorG11.SharedCases
namespace PriorG11.SharedCases
abbrev CellData := Nat × Nat × Nat × Nat × List Nat × List Nat × List Nat
def CellData.budget (b : CellData) := b.1
def CellData.independentMask (b : CellData) := b.2.1
def CellData.mode (b : CellData) := b.2.2.1
def CellData.symmetry (b : CellData) := b.2.2.2.1
def CellData.pins (b : CellData) := b.2.2.2.2.1
def CellData.pairs (b : CellData) := b.2.2.2.2.2.1
def CellData.masks (b : CellData) := b.2.2.2.2.2.2

def evidence : List (List Nat × List Nat × List Nat) := [
  ⟨[],[],[]⟩,
  ⟨[0x947,0x948,0x989,0x98a,0x98b,0x98d],[0x692,0x2a2,0x2b2,0x2c2],[0x813c00d]⟩,
  ⟨[0x948],[],[]⟩,
  ⟨[0x712],[],[]⟩,
  ⟨[0x637],[],[]⟩,
  ⟨[0x613,0x713,0x983],[0x32],[]⟩,
  ⟨[0x612],[],[]⟩,
  ⟨[0x713,0x983],[0x31],[]⟩,
  ⟨[0x437,0x987],[0x71],[]⟩,
  ⟨[0x989,0x98c],[0x90,0x690,0x990,0x2a0,0x2b0,0x2c0],[]⟩,
  ⟨[0x989],[0x90],[]⟩,
  ⟨[0x989],[],[]⟩,
  ⟨[0x916],[],[]⟩,
  ⟨[0x949,0x989,0x98a,0x75b,0x75d,0x98c,0x94d],[0x90,0x691,0x2a1,0x2b1,0x2c1,0x91],[0x813c00d]⟩,
  ⟨[0x636],[],[]⟩,
  ⟨[0x986],[],[]⟩,
  ⟨[0x307],[],[]⟩,
  ⟨[0x549,0x989,0x98d],[0x690,0x91],[]⟩,
  ⟨[0x63d],[],[]⟩,
  ⟨[0x700],[],[]⟩,
  ⟨[0x212],[],[]⟩,
  ⟨[0x825],[],[]⟩,
  ⟨[0x413],[],[]⟩,
  ⟨[0x837],[],[]⟩,
  ⟨[0x825],[0x50],[]⟩,
  ⟨[0x989],[0x690,0x90],[]⟩,
  ⟨[0x413,0x837],[0x71],[]⟩,
  ⟨[0x837,0x976,0x700,0x980],[0x161,0x603],[]⟩,
  ⟨[0x700,0x941],[0x211],[]⟩,
  ⟨[0x948,0x989],[0x280,0x91,0x691,0xc1,0x5c1],[]⟩,
  ⟨[0x989,0x976,0x837,0x947],[0x690,0x161,0x72,0x273,0x90],[]⟩,
  ⟨[0x837,0x947],[0x271,0x70],[]⟩]
def cellOf (word : Nat) : CellData :=
  let parameters := evidence.getD (word/8192) ([],[],[])
  ⟨(word/1024) % 4,word % 1024,(word/4096) % 2,0,parameters⟩
def cells0 : List CellData := ([
  1,2,4,8,16,32,64,128,256,512,3,5123,5,5125,6,5126,
  1034,12,5132,1041,20,5140,1048,33,5153,1058,1064,48,5168,65,5185,1090,
  1096,1104,1154,132,5252,1184,1216,1281,1282,1284,1288,1312,5633,1540,528,5648,
  1600,1664,1792,1031,14343,1038,6158,1045,6165,1052,6172,1059,6179,1066,6186,1073,
  6193,1080,6200,1091,22595,1098,6218,1105,6225,1112,6232,1158,6278,1186,6306,1218,
  6338,1283,6403,2309,1286,6406,2314,1292,6412,1313,6433,1314,6434,1320,6440,1541,
  6661,2577,1556,6676,1601,6721,1616,6736,1668,6788,1728,6848,1793,6913,1796,6916,
  2311,7431,2318,7438,2339,7459,2346,7466,2581,7701,2641,7761,2821,7941] : List Nat).map cellOf
def cells1 : List CellData := ([
  28673,2,4,16,32,64,256,512,37891,5,46085,1041,54305,62529,1030,1034,
  1058,1090,1154,1282,1044,1284,1540,1072,1104,1552,1312,1600,1792,1031,71687,6155,
  6179,1091,71747,2179,2069,2097,2129,1038,6158,1158,6278,1286,6406,2090,2122,2314,
  1186,6306,1314,6434,2242,2580,2820,2640,2063,80911,2183,7303,2091,89131,2123,7243,
  2211,7331,3267,2318,7438,2346,7466] : List Nat).map cellOf
def cells2 : List CellData := ([
  1,2,4,8,16,32,64,128,256,512,3,95235,5,103429,6,5126,
  1033,1036,1041,5138,20,5140,1048,1057,34,5154,1064,48,5168,1089,1090,1096,
  1104,1153,1156,1184,1216,1282,1284,1288,1312,1538,1540,528,5648,1600,1664,1792,
  1031,112647,1037,6157,1043,6163,1045,6165,1046,120854,2073,1052,6172,1059,129059,1065,
  6185,1073,6193,1074,137266,1080,6200,1091,145475,1097,6217,2129,1106,6226,1112,6232,
  1157,6277,1185,6305,2241,1286,6406,1292,6412,1314,6434,2344,1542,6662,1554,6674,
  1556,6676,1602,6722,1616,6736,1668,6788,1728,6848,1794,6914,1796,6916,2071,121879,
  2077,7197,2099,154675,2105,7225,2131,7251,2137,7257,2582,7702,2642,7762,2822,7942] : List Nat).map cellOf
def cells3 : List CellData := ([
  1,2,4,8,16,32,64,128,256,512,3,5123,5125,6,160774,5129,
  1036,5137,1042,1048,168993,34,177186,5156,5160,48,5168,185409,66,5186,68,193604,
  72,5192,1104,5249,5252,1184,1216,1282,5380,1288,1312,5634,528,5648,576,5696,
  5760,1792,1031,6151,6157,1043,6163,1049,6169,1059,202787,6181,1062,6182,6185,6188,
  1073,6193,1074,6194,1080,6200,1091,211011,1093,219205,1094,227398,1097,6217,1100,235596,
  6225,2130,2136,1157,6277,1185,6305,1188,6308,6337,1220,194756,1286,6406,1292,6412,
  1314,6434,1316,6436,1320,6440,1554,6674,1602,6722,2640,1728,6848,1794,6914,2087,
  244775,2093,7213,2099,7219,2105,7225,2119,252999,2125,7245,2131,7251,2137,7257,2213,
  7333,2245,261317,2342,7462,2348,7468,2642,7762] : List Nat).map cellOf

end PriorG11.SharedCases
namespace PriorG11.Bounds
open PriorG11.SharedCases
def cellsAt (i : Fin 4) : List CellData := match i.val with
  | 0 => cells0 | 1 => cells1 | 2 => cells2 | _ => cells3

end PriorG11.Bounds

namespace PriorG11.Compressed
def strict {α : Type} (x : Nat) (use : Nat → α) : α :=
  match x with | 0 => use 0 | k+1 => use (k+1)
def tile0 : List (List Nat) :=
[[0x270d001a110009090000,0x4f0b00441000340d00,0x5006a0500650a005b0c,0x7a04007603007304006f,0x8906008305007e0400,0x9009a09009104008d04,0xbf0500ba0800b20f00a3,0xc90300c60400c20300,0x300d50400d10400cd04,0xe30500de0300db0300d8,0xee0300eb0400e70400,0x200fa0700f30200f103,0x30400ff0000ff0300fc,0x10d0401090401050201,0x3011b04011705011205,0x2704012303012002011e,0x12e00012e04012a0301,0x1013802013603013305,0x4605014103013e050139,0x103014f0601490301,0x1000000000001000000,0xc0000000000080000002,0x4000600300,0x200000820080],
[0x80000300180b200,0x210080001001a0fa0080,0x4000001608100c000,0x700b84c40a00900,0xcc3898274060048001,0x804002400001,0x10080200120000080,0x1006010009000004000,0x420800480000200000,0xa1048024000010000001,0x828012000200000001e0,0x60090000080000718058,0x4880002000000f06081,0xcc0001000028844c20d0,0x8000165e32107004,0x4000003319503c039e,0x2000001c8cc422024c00,0x180ec6721201260000,0x8e370098093000010,0xe4e1e084c049a0000800,0x79008280273100040001,0x89416016790002000162,0x20c00ccc00400003fd74,0x6806ae0020000000fe49],
[0x37a0000400000000048,0xbd000020000000804036,0x80001000000140301b01,0x200000002009a0d80de,0x4000001c05107406f40,0xe82a83e037a000,0x9d7c7caf42101bd00002,0xaa44a2b1180deda0019b,0x255d88982c96d000fa4e,0x32444e296d68004efd1f,0xb62817b8800020000e99,0x158bfe5200100337d499,0x4618a5000801b0cf2e4a,0x39800004000007f7290b,0xc00002000000000285e3,0x1000000040203119c,0x80000006018188ce60,0x10000d0348c4673000,0xc82086433990840,0x32c7c7143419ed000020,0x403921b0cf6d4001003,0x25650e07b3c000080000,0xc70743d9f58004e791f2,0x43e2b52000800400012a],
[0x15a900001080000c97f,0xad4a900080d3f4a4c3a2,0x63500049df897a7dd108,0x8001e00000403f488857,0x100000000014463155,0x800000020102418ae00,0x1b00c120c570000,0xe00849062b800004,0xfc7c4a449315c0000200,0x402592598ae5c001ec9c,0x4a5130d8340000800000,0x449c6c1b68007b275522,0x4f43af000020015711a5,0xa1d7c204000edfc91750,0x3a2c0009d29424ae2a27,0x30840000000267309451,0x201c16943caca4932,0x1f0095cca5eb25549a7a,0xbb271e652b12b2556403,0x3c95c95d2ae2d000,0x2ecb08b0a284000040,0x145a514200002000,0x20102e28a10000100000,0xc171450800008000000],
[0x8b8a28400004000001d0,0xe5142ac0020f9e30f876,0xa1d56001003e84887d45,0x4ed0009c16fe4a56a302,0x400000272b89895f,0x217fdf1919e8c6b576,0x1000000d0d06655abb80,0xa188a469a342d8e8000,0x85936c1a96c7490028,0x28d4b6710800400,0x40206c5b50000020000,0x28362da800001000000,0x49b16d4000030000000e,0xdab6a108020004e00907,0x5ba89c002009e5858628,0x3100001000000443326f,0x80000800000241a8382e,0x13c0009d130dc1c1718,0x2000008a0724e0b8c40,0x13aec64784715c62000,0x80343e939ae314e001,0x108123d1d17b0e000400,0x28ecbd9d58004028,0x4020785fc50000200000],
[0x683c2fe2800010000000,0x9e17f1620080002000c0,0x2bfe528004001c40a088,0x920000200000088484f,0x900001000080482607a6,0x2780027a261403d304,0x4000fe140a89e98248,0x900b8628f6c12400,0x8c4a045947d60928802,0x83fb057d40010,0x10081fd8aa80000800,0x40060fec554000040000,0x1f47f62aa00002000000,0x240b1554e00100400034,0xd8f0400008000010010,0xc7820000400000000052,0xc100002000000080410a,0xc8001001094142108563,0x8000001212242b1e0,0x400d150c0f921d92100,0x2912c909300,0x40208b655b00002,0xf6140e845b2ad8000100,0xb080a2d956ea000822e],
[0x2918cd5a0013c0013b,0x208e66ad000020000000,0x47335680001000000040,0x99ab670008009a41a148,0x5c000040000000004a3,0xe00002000000080411ed,0x4f0002b44c0408f682,0x80015a2804147b4170,0x40000000004a41a0ba50,0x804122d0980000,0x4804091684c000020,0xa2804148b42600010000,0x4a49a132500080013,0x4126d0d400004000000,0x93686a0000200000008,0x9b435000010000005403,0xa1a800008000002c0214,0xd510040001001703ca51,0x2000000000252ad0,0x100000004020966897,0x8000a0340b04b344b80,0x1e1c080a59a25e100,0x861584852ed1cd08004,0x2044c09869078800200],
[0x94c348c4a010006a,0x8265a9880000800000,0xa132d4c4000040000001,0x996a620031e0031d8c00,0x35314e0010008ec64202,0xd9c0000800000000094d,0xe00004000000100826da,0x40020031d8d022136d6c,0x15973b6044349b6b679,0x800000000094eb5ed5a0,0x1008279bba80000,0x1500613cddd4000040,0xac0449e6eea00002000,0xa0325037750000100000,0x65289bba8000d80006a5,0x948ddd52000400037310,0x66f66ac00276f24991fc,0xde65600109f11d05132a,0xc69001007ab6848e353b,0x40000000005aa9f3,0x2000000080415afab6,0x1000000b0030ad7d5b00,0x6e5a02a56bead8000,0x3006d2bdf56c000e8],
[0x499204962fab72000400,0x5182b37de6ac00286e0,0x9535a453250001000209,0xdade2d46900080067c84,0x75185600004002846c4a,0x8c2b0000200000000021,0x158000100000004020ba,0xe900080006a5c0685d46,0x4151492f0a5aea30a,0x20a8a49808a57b19535,0x54524c4592be8e0ea80,0xa29264f415fc7b9d6001,0xfd3785cb0241fa800082,0x9c48498343ef5800435f,0xa444c3a471ac0021affa,0xda62d35d806c00035fce,0x31e9aee900080002a814,0x7555d500040942948a8a,0xb080271202be024d4859,0x40601000010142a72cca,0x10080000b4a355166d58,0x4000000000433aac46,0x2000000080419d563800,0xd4b4040ceab1c0000],
[0x6a02a67558e0001b0,0x36018b42ac700000800,0xb8845a35638000040000,0x922d2ab1ca4004005801,0x969d6fbd2002001420e0,0x52c6900000800600e049,0x63480000400000000043,0xa40000200000008041a9,0x400400008008c0c0d4b1,0x8000007206a6a58d2,0x10ff3a0b8b5ac6e40,0x29af6373001,0x4020d9b21700002,0x40f02686cd90b8000100,0x4b66c85e30008000,0x8041b567680000400000,0x30dab3b4000020000000,0x6d59da00001000000ec0,0xeced0002000000078069,0x768000040000000004b6,0x40000200000008041b96,0x1000075340b0dcb3b,0x8000000000a6e59da4,0x4000000100837acf3400],
[0x1e8061bd679a0000,0x1041f4deb3cd000020,0xa7059e6c0100000,0x100838ad08c000080000,0x61c5684600004000000,0xe2b42300002000d91f8,0x15a11c6100000001001e,0xd2d000008000000000a7,0x68000040000001008392,0x2000d71f0061c969,0x100000001081b0e4b4b4,0x8000000000a725a5a42,0x100839ad410000,0xf00200321cd6a0800004,0x4014e6b5048820004,0x7e020745ab4000010000,0x243a2d5a2200200024c,0x25d16aeb400040000e57,0xe9b5ab00002000000000,0xdad580001000000f4020,0x6ac00008000007c01a74,0x60000400000000053aed,0x200000008041db6b5,0xdf005a950c0e0edb5ab0],
[0x8000008a08976dad5c00,0xe9d460893bad7121007,0x25e16b9d400040,0x910040f1b68000002000,0x206078db404400400049,0x3d3c6da3630080000009,0x5e76d7348004053f96b0,0x4b6dc000020000000802,0xb6e0031f0144951c0f0f,0x72800080a24a901597a5,0x400040382d491ccbd6db,0x200000000025ed7017,0x10015e130020f7bb3400,0xa24ab00607bdd9a0000,0x4bdeecd2018f8,0x8041f176960000400,0x4c030f8bb4b000020000,0x97c5da580001000001,0x3e6ed2c000080000000,0xf3769638004000045a01,0xbb600000200000000021,0xb00000100000004020f9,0xc780510a9c0807cdd,0x63c028854f078be6ed8],
[0x1e01442a80585f576c00,0xa215443a2fbbb60003,0x390aa45717e5db00018f,0x4bf6ed82800080,0x298041fd806600004000,0x12fec0330000200000,0x207fe019800010000000,0x3ff00cc0008000824940,0xf806700c7c04ae74b03c,0x4a0000200000000025f,0x5000010000000402100c,0x18f80a24a9808080602,0xc7c051254d078c030128,0x20000000002603809400,0x281dc12102c04a0000,0xa8160254a0010,0x1008413031c0000800,0xb01a209818e000040000,0x14304c0c780020000002,0x982e06f8000100000190,0x1b037c00008000000000,0x81be0000400000010084,0xdf00002000002a00620d,0x800ba0000815805306c0],
[0x8000000000883e06f,0x4000000100841f037c0,0x8192ab8ae20f81be000,0x16858307c0dfa0002,0xce2e28462430000100,0x442b121a00008000,0x804215891c0000400000,0x310ac48e000020000000,0x85624700001000001500,0xf123a0000800000ae059,0x94600004000006e03142,0x300002000000000221b8,0x1000000040210dc4a,0x8f80a24ab008086e2518,0xc0512559078c37128c01,0x261d894600c7,0x40210fc4a3000020,0xb401887e25180001000,0x401143f128c000080000,0xa62389460037c005396,0x512c4a30000200006b38,0xa6251800010000000001,0x128c0008000000c60188,0x4600004000006d018c53],
[0x20000000002a2b89,0x10000000402117c4a3,0xd808f4a1e0608be25180,0x47a51019545f128c01f,0x2a33894738004,0x40211bc8270000200,0x1c0608de413800010000,0x4c6f209c007f8023da,0x8239904e000040000000,0x1cc8270027e0027db400,0xe41380200000001a4063,0x9c0000800000d403a8e,0xe00004000000000547f2,0x20000000804243904,0x7f0053e5ac06121c8270,0x8045ead806190e413803,0x22f56d048c8b209c01bf,0x2647904e00dfc0,0x402124c82700002000,0xe0189264138000100000,0xcc93209c0000800000c,0x24b904f18020000a06f0,0x5c83700010001783800a,0x41b80001000001b80112],
[0xdc00008000000000892e,0x4000000100849720,0x2000000f00624b906e,0x13cbfc7d50525c83700,0x1fffe6eb8493e41bc608,0x5caf3ed408000,0x80425d9f6a0000400,0x740312ecfb5000020000,0xa9767da80001000000,0x84c33ed4000080000000,0x619f6a00004000000100,0xcfb50000200000108062,0xdac608010affc88ff530,0x20800043ffe7092c9967,0x40000000005cdb560,0x20000000804273abbc0,0x8003139d5de000,0xa9ceaef00001,0x10084ef5778000080,0xbb832277abbc00004000,0x3353bd5dea000202b96,0x4a9eeb6fd0001015cb5e,0x4ff5fee800080ae5af22,0x3b1e75000404fb97a215]]

def tile1 : List (List Nat) :=
[[0xbf0000020000000002a8,0x8000010000000402143d,0x4f80165a50060a1edf,0xa00040001150f6fc0,0x200028010050040008,0x140008000a200014010,0x4000500200a00800100,0x8001000040008000200,0x2000414010010000,0x20002804000004020,0x40008000200800001,0x800050020000080010,0x800180014020028020,0x28020004000100200a,0x10002000500010000402,0xa004000800140100280,0x1002801000200050400,0x1900400a00400080014,0x2fffe000a40000,0x32080000009000000048,0xa00401000014000800,0x40800280100100000880,0x50010320040004006,0x80014010028010002],
[0xa002014008001000c8,0x40000281000500200200,0x20004000a2000140080,0xf00054000000c8020050,0x80200281440000001fff,0xa0800140080010002,0x800004400050020080,0x200020032040014008,0x2014008001000c900019,0x4000800140004000a00,0x4000a2000000080400a0,0x10000000402005002000,0x21000280100020005,0xa050001000c82000,0x400800002004028011,0x4000a10000000801000,0x8001000280200500200,0x50020004000a0080140,0x20001400804000028020,0x4800050020100000a,0x40c8010002001904000,0x802000028002000640,0x50020004000a100014,0x10001140080100002802],
[0xa004000800140004000,0x200001010000008008,0x80080a00400080014,0x10050020004000a04000,0x1008000008100000280,0x80000400400002000428,0x40020280100020005000,0x500010a0040400001,0x800014004028010002,0x8010002000500010a004,0x400a0040200001400402,0x14020028010010000500,0x81000a004008000,0x4040050020020000a010,0x10010000080106400,0x800004000800140020,0x200040001000200008,0x80000080200000400080,0x4004000020004000100,0xe1401001000008008000,0x20023200019002001,0x50020004380a00020005,0x4014008002000280080,0x4040050020008000a0],
[0x107ff0005080000,0x52000002303ffc701408,0x118080028010002000,0x40005000100028001,0xa0040010001400802801,0x400008c1000000080800,0x4602000a004000800140,0x50020004000a3fff00,0x1004014028002000c810,0x4010000024000140,0x800001004000008020,0x1900403200500000064,0x40000640100c80140000,0x320010015e0001320040,0x3200400807064000400,0x40040000100200000810,0x14028002000c80008006,0x8500a0004c8010040,0x500020000800100004,0x1000040008000200fe0,0x2000400010200000280,0x20000800100004200028,0x80080000200080005000,0xe00201c0080010003],
[0x100038008070020004,0x20004000e00201c008,0x201c0080010003800807,0x40008001c0004000e00,0x38010002000700100e0,0x80010003800800002004,0x1c0040000100201c00,0x80000088000e0040008,0x400800002004000010,0x4000100200000801000,0x8010000040080000200,0x2004000010020000,0x200000800100064008,0xc80080000200400001,0x4000108000a0080020,0x800100004008000020,0x8050020004000a020000,0x10020000500010002800,0x4008000020400280,0x402805000200190010,0xc0080008003800800002,0x8001c0004000e00021,0x10080000280400e0040,0x1050040200000a000414],
[0xa0100000100200002800,0x28040050040008000,0x2000002010014010002,0xe00800000804000004,0x40320040008006400040,0x20004003203ff007d00,0x200192000050c8020000,0x80201900240002805000,0x32008014028001000c,0x1ff803e8020190020004,0x86401000001000200190,0x14028001000c900002,0x14000800640100c80140,0x3c010020000780400a0,0x84000f0040080001e100,0x1e10003c0100200007,0x20000784000f0040080,0x436e1536aa004000c050,0x10a8a84142b3806d41ad,0x8a8a8a85155728a954aa,0xaa5554955452d52a8a8a,0x610e1c3049214941612a,0x554d52abc183b9839b98,0x6402a01200300140015],
[0xf8ffbdff6bfb3fd4fe78,0x7d53ea7f35fcd7e67f29,0x5e84f406e83eb5f59fac,0xb747f9bfb9fb4ffa7fd1,0x3fe5ff257913c81e3af1,0x6ef87bc17e0af02f47bd,0xa9dd4aea0f4c7bbbdbab,0xe88741b9e3a5abed5a6b,0x6d33659fcd747fa33d18,0x4e586a674b3919c6cdf6,0x7b90d518fccfd679bdcc,0xc5dd8e55722bf18e8c72,0x4531a9f95faaef53797b,0x3d3fca7d53c29b95dca6,0x6a6b50b910fa9de4ea27,0x5d0fd18643f19ff50e68,0x5e64f323980d0c683b3f,0x1795fca7e507281930c0,0x25647b21f900f45f92fc,0xff77f6c1df727693e8af,0xfc37d1ba0d80bc036016,0x7a03401fa27c12f8b7c4,0xff2078032018c0f20f80,0xc3963e36efdf4ef8ff9f],
[0x3958aa5429a0a4350c71,0xe3e3ff8f801f8f8f3f84,0xc7f1fe007c7ff8ffc780,0xf1018f8ff8e038f1f003,0x80006000c78f00318f,0x7ef7f7afe87f14001100,0xbbedfbd7dd7f3af987e1,0x6afb579af487a3fceda5,0x4ef257907c81e3bd4d69,0x966fb3419f2cf943c9fe,0xdabf0cf843c15e00effe,0xf55baabd54ea0f727b81,0x3d00e7ff3af72b955c8a,0xa6553a2dd15e8a744fa0,0x273d3e6b7357981cbfdc,0x2726b92bc70e35e54f2,0x7a9bd3de2ef13521c14e,0xdcaee53727e4fbe7ef57,0x3515a89d6d6b67689b35,0xad2cf92b495a9ad4cea6,0x1b98d995cca67d6d13a5,0x55caa654f2a194ffc374,0x4171e3f85fa2ef1770b9,0x8b5c8ae45321f90ec836],
[0x606701fd01c2ce35319f,0x37cff207403981800c0d,0x872ff8ff63fa7fdf6afb,0x1f7be7df2efe79798bb,0xb8d53aa95540f9b6ddad,0x214d64718f7af9d7dacf,0x18307061b3491f6e557,0xff70f00383ee1fef0ec,0xf060060ec3e86007b87b,0x100383fbc3ee18014361,0xc000002e08001bc3bc3a,0xf800304000001000000e,0x7affe7bf3cf9dfc7ff3b,0x3d40eaffb77db9edbf6d,0x71fb8f5c61e70737b98,0x3b99bccd660b4fda01e0,0x61d4fee79722bd1667b3,0x4f7262970cb8e9c14dca,0x7cdbe69f07002900c9f2,0x61e0c0342eaafda46fa1,0x6d83a0d07d436ec3ef6b,0x2aaaaa94a4a4808103d0,0xaf7faf148802000aa955,0xa7290620830027f4d17b],
[0x88394831056942d28398,0xe62910562d285a507314,0xe01f807f4b2b62d2b4a0,0x1fc03001e01fc03f800,0x387dab67001b1618694e,0xe7314aaaa68a82bea71,0xa1b7f7fafe3e576fdb72,0x13fc8d0338ec52769d26,0x5badff7e58d62d8142d0,0x45a94e3bfcdde777d5ef,0x2f83d69b1f87d1ec7317,0x3b86d9b3e5993e4d35be,0xf331585594e35f61d36e,0x53bced3ace336cd935cc,0xd42d0940d013fcf93dcf,0x147d1d465174551343d0,0x10662208d2b4a52748d2,0xfffefffffdfff7ee1689,3967,0xfffffe00000000000000,0xff3fd7fabf07ea00007f,0xfe69dcfb67cbf85f07ea,0xbdd57aa753e9fd1ba2f5,0xc9b92f3febfa7eafcbf6],
[0xe1fc16e6bcd398f30e4f,0x3f06e07c039ff5fabf37,0xa0d71b7ebfd5f83efdb8,0x80da1740e80d35aeafce,0x59ef4d6bad359eafd4ba,0xeb4d5fabb536a4d41a40,0xfd5fa9439f73e67aff5a,0xbf54197aefd615eabcd6,0x9bebd579af15aab2d60a,0x6bc565ac157c17eefd5f,0x5c157d75febd579af55e,0xaa8750e61c42a83feae9,0x8750e6154290d40abf56,0xc297736a6ccd89ab3526,0x9692aff5fcbf57a2ef5d,0x7aaef0cbf9772ea5b4b5,0x190bc9692b22ff5fcbe1,0x83686a8d0561a42f84dd,0xc1a82d0560a406e8dc9b,0x6e4da9b43666acd0020f,0xdc9b436617cef9bf374,0xdadb0fe1f83c0740e619,0xda0fe1f83a073037f6e0,0xaac6582b1570fe1e98d2],
[0x815797f2502df5b6b596,0x47c8ed1d23946a8de6e4,0x485d01217fafa5f3bdff,0x3097d2e6f7ddf021b43,0x128440e82f4a82106811,0x787c37a1bb6416454,0xe10000ff17ffc3ffc380,0x2fff87800062fff0ffe1,0xf8000078dfc3c000387e,0xf17ff0f800007f8bffe1,0x800061f8bfe00001c5f,0xcbde3f4000022cbf,0x17bc6630d593e1000300,0x8a1c300941e8014003af,0x6a86a0a7e9f262972588,0x9ca321c82b0ac0a8a9ea,0x80541483406801fe4c72,0x6a02800c0250921e8781,0x8a6097a5a9623a8e2268,0x8a9ea6a98a1a82a027a9,0x9c2301ac6b0ac0aeab8a,0x1cc3304a728c8718c490,0x68541483206013fe4c93,0xe0b2250921e8781d05e1],
[0x21a81a02801fc7e8ba2,0x7a9aa1a7a98a5e96a429,0x4a721c431040700ac0a,0xbf9dc8f3f9bc2131cc33,4194303,0x1fffffffffffd00000,0xffe80000000000000000,0x1fc47ed4000a3fffffff,0xf45fe17f80fdd5fc97f2,0xe7439c8e6f3be707ae9,0x67915e3b78e9e307899e,0x74c3dfbf7ebdf0f7abde,0x3c7f897539d4974f9d39,0x85ccaf43bd09f423d00f,0x1bce6e87c0df00fbfaef,0xa8aea17a76e9c7a706a0,0x30648398ee60f97ee5c3,0x1ded58445fd994965159,0x63c3cf1e4c77f6df9b7e,0x663d21cfd767ad9c5e70,0x11f3f00f9f3d208e7997,0xc039900f1e007c2018f0,0xefe2ff00001000000618,0x6efb7f8ffc2fdeff9ffc],
[0xdafa37d17e81f3ff2de9,0xf66d33419e8d6a6b4b57,0xe8ef405562831a99c0cd,0x793fc95e41f207a43d1f,0x7d16e6b655b22de5bf28,0xade57c21e0af00f7ffbd,0xabc95dcae55722b8d5be,0xaa64531a9414ee074579,0xfa74139e9f4539a9b94c,0xea0f503a77d13ca9e44e,0x7a03d00e7ff3ef9f5d55,0xaf08f457a29d13e83741,0x579a9cc6e6072ff977cb,0x95e407943c21910be873,0x43f19f80fbe7d53f935c,0xbc5ddb7a3af9d40ef27e,0x6e17709b7bdeaef537a7,0x3e4af056a2b49568adca,0xd6a67531a90d456826d1,0xdb46d2d6967495a40d4,0xe2ee16d0b9f5fa3741b7,0x2a9953ccaff17f0bf45d,0xc8ae45321f906c78e557,0xfd03e41f00f707a03cc1],
[0xee07403981c80c6a633,0xfec7f53ffe07d03c81e0,0xd9be7e06b033813c07f2,0xdf3e79cfce5e5f6efb57,0xf3be7df2ef8f753bbb87,0x6ddb46d689b42d3ebef7,0x554eaa067d71eb8b5f9b,0x8f2c71e37b1a8553eb1e,0x59cece565067e63e31e7,0xb5fdb3e59eecf1677b3b,0xe82d08410f8afbd7dabb,0xaaa2668b1e46494a458,0xe0f307c1e3ce383c2d73,0x23ff079f83f89ff1f3c7,0x183e01e0f80e0fc73c7f,0x8cfc7c1c101f89e3c1f0,0x300083f13c783c0707f,0x3fc020000fc646001c1c,0xdb5652f5555295d4aa78,0x341580d02c0695f170de,0x50ab45b6d16b60b682a0,0x80a0340681b40506b42b,0x97491f00ac0701f00000,0xbafb2fbfbbafc2fb7bb4],
[0x7f6c75c70c66c51afab3,0x762f6675eb5e766f6bb6,0xa71271af1426425a752,0x3be39be6b6eb66cbfa27,0x67b273e72662e77a73bf,0x3b7ab79b75b74aa63266,0x340334e61a61661e6266,0x57658affaefaeaae525d,0x2bd22bf2be2b42a52a0e,0x3d1a7ea79a60352e92ad,0xd8793a6860cb9f754a24,0x27b2d1476020c4286954,0x55740d0f8090f0086c11,0x9f1f0f8f8f800000431b,0x5d5d4dcdcdbe3e2eaeae,0xa955510b8bfc7c6cecdd,0x2c006000aa5a2955554a,0x8bfdffee5fc6fdd7e73f,0xd0fe77f2e7cfbe5df2af,0xf2178ebc71e36f177857,0xfc07df9efbf7a7ba5e46,0x5e79f3aba55db6ec9f81,0x3969cb2e55f417a03cf,0x85e3af1cf8d7c5ee6273]]

def tile2 : List (List Nat) :=
[[0xdef6ebb66de06eeb76bc,0xa62d5b6ceb64fb85dc0e,0xe78b479a38d16688f4fb,0x38e9c6de353289935cfc,0x7628b137905c7fe3d71e,0x377f1bf4df931698b0c5,0xb4dd6af8d7bcbd65ea2f,0xc6d621b36d996cc3771b,0x9e8d3ae9bb4d8aa35472,0xa769391a02cfd67db3d5,0x80f19e6cb4f9ecb43d10,0xc7ce01f3e3e418fcfe3,0xe0073e380f8fe6019e32,0x694200c0031f00398018,0xc9fb3ce6640b798e2d0,0xf8de1fc376ede7616a65,0xc8e0fe9f83ee6f4dc0c2,0xca744b395b1ce36c2e65,0x19631c5d8b71161de3b3,0x63dc798ef1c637c6d8cf,0xbc9591f23645c8590720,0x1fffeffffdc084432664,0xfffff000000000000000,0xb005f62fc4007f080003],
[0xadcd6eabb37a6f2ce99c,0x2ce44da9762ebdab9cef,0x3ae73ce17ccf95d339b7,0xfd0760ead5ae95d26a43,0xb7d2fa2858eb1111b826,0xe7fcdf97f0fdcfb7f5fe,0xfedfd7fa7f0fdffb3f5f,0x2003ffffeff9feffd7f9,0xdffffdffffa190211000,7,0x2000a0006fffffe0000,0x3ef9f78faa7d43e00068,0x1f2af947c7be14fc87e3,0xebb55da6ed17597d4bea,0x90dc66caf97fcbbe5bf1,0xaf7573a8dd0a6e93741b,0x83ecdd66db2f5966ca8e,0x5e32e7f8bbc5be23f0a7,0xc0fc0fe07a28e17b4bd0,0x4d3f80f81f03c0f80f03,0x4a52555254a8aa2a2ab,0x515aaacaa998cfcd0011,0x400b682da85a05a05a8,0xf2f4e7cb8f0ffd828406],
[0x1fa00fe45c98f161c1b,0x70a10101003c381003f4,0xe1ffe7bf5c7e8c162848,0x9cf87ffdefd79edd7a71,0xbf66bd5875faf3e3b75e,0xf06fddaf569cd97261c1,0x7c0249bdead3a3365c98,0x7fdffbe0000000007ff,0x2a2ffdffbe00000000,0x768360f03dffa0cbc01c,0x6000ff9673b0cc9683ff,0x940db80eb03689793248,0xc07f80ff02493338b24c,0x27279fe7f80ff01fe03f,0x49330112493264c993,0xc6efb9e7bdc06ffbfe7e,0x71de001dc7001d073f,0xa7697fff1bafe9f5f840,0xeff1fbfefc207bdedf41,0x1209fef69dcf93c27877,0x3befb0003e90009beef1,0xe34da96f169e1e026200,0x169e016a5bc5a787800f,0xbfe82d4b0078780b4f],
[0x686421000338001f3f80,0x86530ffdb864330eddb9,0x8e1c3c70f0f1f3c8731c,0x2e0c1012322c6e0c0c30,0x349140f38d30b8df75bd,0x7fe1e18e18431aa51,0xe83d90e81b1f05d0f81f,0xcdff9f6bbbe73fdf7bbf,0xce71adef5ccf71edff60,0x4aa54552a8a9554ddf58,0xf003e01d1bf975f1f015,0x1f746dd7c3777e3eba7d,0xc75f1f5d3ef805d3ef80,0xa8029558e99d5d7c00df,0x782500812b6db402ad6d,0x6716499249781e0925e0,0x1621628b174091094926,0x7b00a2f86520cb9ca10b,0x311de291eef0c40fbbcd,0x73d823148ee7dcd73180,0x1b6eef24749b629282,0x3e98080000136732200,0x800f3c0079e003cf0f3c,0xf3c0079e003cf001e7],
[0x54a952a54a8a539e1e78,0x71bcf3feef062080452a,0x4200003d001b800bfd6,0x1e00ec06103001740b8,0x3f83041020410007d03e,0x7d7febbf5cfad7c6fe3,0x3df9dfce3e6ff33f97fb,0x3cf8fbc75ea2fd13e87f,0xd47ea0f503a71cfce7a7,0xdd0ee07743d1befef693,0xc341a81d2fe96f549ba3,0x1a00ffc00ffff003fff6,0x343434340003801e0000,0x2554aaaaa49937434374,0xf5209412023044028000,0x1fa3d27a3f45e87c9f84,0x9b8f718e53f7beefdcfb,0x4d759eb1d5fb4f28e4fc,0xe09c29b4f696d9d31a5f,0xcb2794b34624c4788b10,0x3b43ee75cdbd167aced9,0x536a4d68a4f49a91d1ea,0x6644e993d2764e48fa9d,0x446884f08e0cc1882f02],
[0x9271ce35ca44e8951262,0x63cc758e304786f51c9b,0xaa254429d688d0db3b26,0x790ea245a6bfd7f2dc51,0xc498837e9f93422744c8,0x1fa3f27a0d31a3344684,0x8fbdf77ee7d8f9ff3be7,0x44063abf5e2f45e4b4fe,0xe8f716d4da7b4b720230,0xb8a653ca598fd17a1f27,0x7dceb9b7a794727e4dc7,0x7fab1a5f545debb9762e,0xc4588709e0fa9d536a4d,0xd676ce59499332272623,0x6691c4e8951262445fb3,0xe23c37d34a293d26a3b4,0xb44686d7a4ec9c93cf25,0x45febf973c2683105e13,0x7e9f929b9271ae8d712d,0xae8fc9e764cc798eb1c6,0x90721e2f45e4ac28d510,0x4460d02204111a134e89,0xcd1304af2748b1e46995,0x70f03f0f81fc00fefa38],
[0x6078781f8703c303f0e0,0xe1b078703e181f0f81f8,0x7c3818583fc2c1fc183,0x781c3e07a303f87c0e1e,0x18e0763c0e1c0f0fc0f8,0xf7f6800c00e058e031f0,0xd5778f97eabedfed001f,0x6fdde9b7bfa7e4fabe57,0x36335b376abd35b6f5e,0xebc703014020012ad000,0x2828280401c07c7dbfdb,0x666512828282a8282828,0x81a03203000033326666,0x3fb5e67cc78af13e700d,0x3fc7b8ef1ffbdf57ea7d,0xa3b4f755e9fd3bb0f20e,0x305e1adb3b2b64ed0d1f,0xad94b2762b24e5ac3386,0xcfb8d716e25d9b3165ac,0xa3b4568a513a2141a8ad,0xb25249c85a89502afd1e,0x6665cca9833027fcf09a,0x3fc5f83d03e074098353,0x3fa794e25c239a88b102],
[0xa6bcc758ab14626c55e0,0x2686565af558aa115fab,0xfc0ec99836a97d0f21d4,0xb0fdffabf53e9fd0f8d,0xa751ea1d3faa95429c5c,0x1c0360680c80c002057a,0xf15e3365ecad93b07700,0x192f25649cbfe6bccf98,0x12f85dfe3dc778a70fe3,0xa054fd1da56e85c7b8d7,0xe18c1782b04e06a8b512,0x3b17306604dfc3786b0c,0xb312e22c408ff17eca59,0x205fd3dfa3d4768d51b8,0xa0d40f81d07daac94927,0x4b85708e6965aca5bf07,0x1d62ac5189b10632929c,0x52272ce31c13f67c0ef3,0xa8550a21528c511402bf,0x68cc9983006fccfa1e43,0x7e1a85511634090123e6,0x1fbe8e8358c12c8a0238,0x86078781c3c0f87c0f80,0x1d07c3f60e1c0ff0f81f],
[0xe083041e1a0d083e1a0e,0x47c0f0f81f0fe07c3a0f,0x14781f470387f81e181f,0x8683d8fc08781c3e0438,0xc6b5c403d3000fa00f81,0x13f2f211fe1c18e8b7c6,0x1ffb08f817f6f614,0xb85a2c10f86c01ffb000,0x90c7a3b1c8bc4a22f278,0xfff8000f788fe731,0x6c001b0006c001b005,0xf91f00102a0b6c001b0,0x4d8173e1d92e99b1f15d,0x8ef1cff6deefe935d055,0xcce14bd7d6adf989e75a,0x2529494a529294a55052,0x25d3363e2ba1f23e0025,0xddfd26ba0aa9b02e7c3b,0xd5bf313ceb51de39fedb,0x525294aa0a599c297afa,0xa8f98f8004a4a529294a,0xf7dfd741f0ae9cd87c2b,0x7acb7b319e7ad43ba397,0x802955a944b5708a54cf],
[0x9d2ebe000f9f2ebe000f,0x9f3a2e8b801f2cbc3e0d,0xce401fcb9fcdbe098d8f,0x5f2e800f9f1dc00faabe,0xcd8faf7eee8e7e001fef,0x8faf5d1f3eee8e7e001f,0xc00dad7eecaebe002b4d,0xab4d9d0a6cae8e7c3e1d,0x8b801b0fbcec8c7c1dcb,0x1f2c8c6ebc3e0dbceaae,0x2aacbc0bab4d9b0fbadd,0x5d2aacba3c09be1ffadd,0x9b2f59fc09be1fcd9b2f,0x2abeec99ce7c09a95fcd,0xbeec8e7c099dcb9fef5d,0xce7c099dcb9fed5b2f6a,0xcc4e499dcb9fed5b2f7e,0xe5bddc01fed6f7ceabe,0x9deb5fed6f7ceabecc7a,0x2b6d4fbafcfecc4e5bc9,0x6e8e5bc01f0a4c499dc0,0x6c99dbddeb6d7aef7ecc,0xec8c6e99e94fbadd3cca,0x99dbe9403ad9e95dfafc],
[0xe9402b4fbadd1f0a4c6e,0x9b3adf19fe297acc59db,0xbadd2a8a59fe294b9fcd,0x9d2abeec99fc3e294b8d,0x1fdb2cbc295ddfdd2c8d,0x1fdb3ccbad6f7cfece7c,0xe499dc01fef6abecc7a,0xeb5ffacc5bc9ad6f7cfa,0xfafcce5be95dfcca7ed9,0x2e99fe1dc00d8fbcdf1b,0x1b1d2c8c7c0dad5d3cdf,0xca49be0faaba19fc0b80,0xce5fef5fef5fd9fe1ffa,0xca5deb6d7cfefedfef7e,0xfced7cca4c5bddeb6d7c,0x481619e97ad9dbfacc5b,0x600b114525241c740cd1,0x12823241a7c4e89b7334,0xc375650c216fabc5269c,0x2264801300200000005d,0x200804040004a4cc295,0x6d6acda966949243254a,0xdb5aa8c99965b2ad751a,0xd6d35b6b516b5aad4d4a],
[0x5ad6adb5aadab5a56d6a,0x898ad92daaab36a1a5ad,0xd5d364ed526255ab6b58,0xd695a2909554a25a484a,0x5599d4c429586a324c54,0x20400128014524d6532,0x54c2a500849440000810,0x4004800880212410269,0xc81802a04c0800f0140,0x2704808c1101f03a068,0x5001ffc1682c0540a414,0x2804c0800f01c0240300,0x880f01d0340640c0150,0x41602a05009c12824046,0x1fffff561005c0b,0x801001ffffff40000000,0x102003c0600b01401802,0x4007c0f01a0320580a81,0xa81482804c094120230,0x80a81001e02c05005ff6,0x202303e0780d81a03205,0xfffd5840150290500941,0xfffe80000000000003ff,0xd8281208038180a04007],
[0xb5da2cf66b2d92c762b0,0xe0602810060200803fec,0x4aa451a8942a0a048200,0x7b7d9ea62ad52a853a99,0x1586fe9f3f97c7e1eff7,0xcb5daad368b3596c963b,0xe1eff77b7d9ebf57a7d0,0x146a250a817e9f3f97c7,0x416aa54aa14ea652a9,0x1ffffac13e6f2,0x1ffdff80000000fffffd,0xa3e003ffdfff0000000,0x35a8c9405d6c3c7f8a16,0xe675bb93478138904008,0x6e3ff55feff5080c320e,0x3d9ac067a9554592c978,0x46b759a89bcf67f148cb,0x1080743817f97e3eff9d,0xf60a2bd1e0f66e98c241,0x6337eeef437fb2dfec2d,0x51a2820510ab4208e18c,0x90704043d8d8d80d0c5c,0x64be7ff77b7d5e0065a2,0xb69e6d38ac339c65e2d1],
[0xa8b21508865007030371,0x98f7f3e9e8f07b3c22b1,0xff3f8fbfd3e7f4b1da70,0x9b7b1d7eb767bdd2f8fd,0x5dac966bc6eb71a4dd26,0xb6dfeda4b2493506814c,0x2993cb65721bedaed367,0x40dc09e0d2beae9bd657,0xf5819f42ae0540c40604,0x5f62f57071d0b8827a9a,0x955555555292cf474aaa,0x1442200688884501252a,0x3aa2232211ab440d08f1,0x59d4f8fcd58d06845688,0x9ce49e618b6048201f43,0x2f3ebe79cfd7080007,0x96d425449bad6b99d600,0x44aaaaa4500011555524,0xb1f54458f4f4768ea475,0xaffc0bf75400001bdeda,0x44fd4adb5540556aaa52,0x9aa900d5dab688e8353a,0x54ac486df72f2f2010c4,0x6453f6ec9c36c022aaa5],
[0xd3c632f2bf3da45a1a85,0x73de5510c49363367418,0xe001f00c13f9f4014055,0x99bba7c9b5d7c3e5d1f3,0x436551736f817d9f8bad,0xa5294a528a9937493557,0xcfc3e1f000045294a314,0x10bc21f425d1f3e1f7c6,0x1421f6ce142519f3e1f6,0xefc00425180421f0f9f6,0x10fd1d1e12e8b805d51a,0x1800bc22e8bcdfc519f6,0xc5d005d00708be17c005,0x7402f9d6cdd5d5d1f2ef,0x56592aa2c9228409000d,0x59214a89a50b66b52a2a,0x10050aa958842152490c,0x3c008f1e3c5a3c0000f6,0xb40796e9ad7800cb5aad,0x1e005a78e93c96433c25,0xad3c00cb1e00cb3c8f,0x433ccb1e8f008fe9ad3c,0x3c1e1e8f00e95ae95ae9,0x5ae9cb8f5a1ead00cb],
[0x96b4ad785a3c96cbe978,0x43070025b443e9b4b478,0x5aad3c001e43008fb400,0x78963c8f1ee9cb8f5a3c,0x80881b4396e9073c5aad,0x56b5edda8cb9184a0419,0x928554d9579d2a8d0052,0x575a33a324d7512eaf6a,0xe28292aaac10195a8317,0x30c3ef2bb78b51785acf,0x100800555514da83eda1,0x6737a79f978ff7b02018,0x7e36aea6f6b72f1f1707,0x4d1585d5cdb62e260e06,0xb52d251d150d7d655d55,0x46c4c34aca49c948c84,0x5b3393f3b42c241c140c,0x9282fae2b32b23130373,0x918981d1a2120a024a22,0x1f401fe9523b2d9231a1,0x3f7c01b007d007401f40,0x7600fb006803fb007f00,0x1ec049215697e803d00,0x1efb71d803df6e203df6]]

def tile3 : List (List Nat) :=
[[0xdb8eccf8807bedc76670,0xae80f7db8eccf8ae80f7,0x3e2bb62980f7db8eccf8,0x71d99f15db14fdf6e3b3,0x2bb629f1d99f15db14fb,0xc576c53cf8aed8a7b33e,0xd3e7f2b8de9d8a776c53,0xf80be02f0170160280b1,0x7f807fc0005fc05fc05,0x40300e01e01f00fc03f8,0xdf48ac5a0514083c618c,0x7829e29701702e1f81c7,0xee95dd2bb82945407285,0x57732ee65d8993993a72,0x2f2e94e1e0b9cbdcbdf9,0x372eea5c5472e6e508a7,0x435c4cbb132e16e29cbb,0x9c21441148f05ec43d88,0x39a211ca1ab286a28422,0xbb1165d34ce6bb473eea,0xa358959e2311761f7166,0x1f7c33177becab35a1b0,0x18680edb49264a408247,0xb54f4d11a3f4de308a52],
[0x6a34839f3759bc68d885,0x22a48905148228806989,0x5953b1b2d2c98b8a28a4,0x9b4dd3534db359adb453,0xdaaced9a96ae9a9a9b56,0xb1dcda6e9b2b36d5b355,0x3b9b66d9babb56cb65d3,0xa3469716aeead2d2ecdb,0x51a054922d8a68d14d4,0x84214805094508860114,0x42a994b85d49c6511080,0x732ee65d94ce4ca790a5,0x85d2970de25ec4ac4622,0xb372eee689ca547212a3,0xcf8997626422dc65e3a7,0x414c1a989e086f621bd9,0xe7d17c545850a399ab08,0x6bc6a0cd780b8c239a94,0xb32aaab13a46231e37e1,0x902310791a10f633dfc6,0xae4a9a688b1f46e98250,0x8215012880bfce8354c6,0xa6ca96951969518b2a04,0xed5d4a5969a9d4d1a54d],
[0x369ba6aac6e66ad972b2,0x946d96ac54d668ed3b4d,0xe2d36363b95cdd369aae,0x8428622ca18690923a30,0xaa6121800800900a2028,0xc0229555554aaaaaaaaa,0x374fa7c02e86df374fa7,0x1646cfa7e5fe166e86df,0x50002dad80006b6a25fe,0x4f805d0dbe6e9f4f805a,0x4f804bfc2cdd0dbe6e9f,0xd6d44bfc2cdd0dee9f,0xe9f4f805b360005b5b00,0xd0dbe6e9f4f805d0dbe6,0x6d44bfc2cdd0dcbfc2cd,0xe8c005b00005b5b0000d,0xd8511e01a3001b088df2,0xfcac21ca6e87c4230930,0x73e91e8d9f4462307dcf,0x6c272f3ee17cb4fc8d61,0x446c207d804c3f2d3e00,0x801611bb30909eee7d00,0x53f001bbcfe00e17bab0,0x220c51618bbab97fbb9f],
[0xb1ccb4ac6951a4ca8668,0x2080001060000f0b8d4,0xe0a000a0900060900,0x5001407001308001208,0x1c060019050016060015,0x1f04001e03001d0300,0x9002407002205002007,0x400800350a002a090027,0x430400420700410600,0x5004805004605004404,0x5002004e04004c05004a,0x5a0700540400520600,0x8006202006102006004,0x7401006e040068010065,0x8105008005007a0500,0x5008604008407008203,0x9803009603009402008d,0xa90300a604009f0700,0x300ba0200b30500ac01,0xf60200e20900ce0100c4,0x12a08011e02010a0900,0x2092492461400004,0x855935200dc000000000,0xca00000000000001565],
[0x20210738d28000a24f34,0x3d355140b0060540438b,0x55344235443415556447,0x976544cf3d44d23d028d,0x944911d259b5522d10d4,0x800043533c46100d5145,0x413c8448f1800074512,0x355b7d74473566135440,0x56543c928f5d44c5e828,0xa6932981c51d75848b31,0x84400f51669648e1d979,0x4c20884554400893914c,0x1505575d0085240473d4,0x418649f950339265c683,0x1661a5ce28e490611145,0x585d20d355b7180ce2c5,0xc000028b30c2100b4115,0x3214028b1c000624d2,0xcb3d130018b3cc3470,0xd28b2860003cc28d061c,0xf34f007368cd50d34b00,0xe3200218b44b28908940,17126984,0x39044d39fc0000],
[0x8410ebb000000000000,0x50071c61c7204,0x8024a2c920c2091c83be,0x30c40c308f590000001,0x43e2830811030c31041,0x30c30400031041030c41,0x20c30c410fb910,0x60800003f30000000000,0x20000051c61871860c,0x14618610618515,0x10518614340ec30c2,0xc30d058000000000000,0x40000000000000000000,51131416,0x51506a0000000,0x8f41d000000000000000,3,0x51430c71c71861109100,0x51854394510318718,0xf500000000000000000,0x20b20618314a2051c105,0x724745306041,0x30b21163000000000000,0xc82ce30e24d38b288309],
[0x4d2cb30b38b28c38f484,0x30d312d830d30d3,0x8a4bf400000000000000,0xc34d3ca24b2ca24b2cb2,0xb34734a28a28b313af30,0xc30e518c929030d34,0x48900000000000000000,0x31048a3494503cf34a15,0x44c3d12d24c954e42083,0x34e356022962472470d0,0x8d45c1d054a5951543c5,0x5a30c5c92962491cf5bc,0x47417255397e51554595,0xce6385860a1433937553,0x548f3903435568ce48d4,0xf4520c30cc407299d81c,0xa0ce0cd6a14c48b2c728,0xb323831d338c4450963c,0x40c1594143100ce59c39,0x24575964d3c57135b797,0x65351d473cc1cf5d740d,0x4089948d3c85a3252387,0x861860c7086106004798,0x820c40840de9d0801020],
[0x47b2030c30821001020,0x62031870871000c21041,0x21840821820c221f0c10,0x21001827d4c21c220624,0xf8b18610008408510708,0x1020c40071091840c409,0xc41401860037f140006,0x1dff71050030830c3,0x2003144104000102084,0x82185183100086180808,0x82070c60a05d1c81000,0x8826030c20c41040020,0x71461871c41801830c71,0x2092882460e0e700,0xd20b0018470000000000,0x15800000000000000d38,0x10414414212,0x304400200285d00000,0xc312180000000000000,0x47006106142143182144,0x3004083180870,0xc00c50c61a1d30000000,0x80881840070061020020,0x40020021],
[0x41451040c60851221400,0x5102140896450061051c,0x26b00000000000000200,0x1010c20c014110200006,0x51001008a383006,0x629b000000000000,0x80003000040000080000,264360,0x410410410a2a30000000,0x808ad410020410420410,268502032,0x10800c20431470e2bb00,0x20400c18b9440430c400,0x2f600000000000108508,0x4104004000000008006,0x410410400838c082042,0x1450e30c000000000000,0x830410431851430c3185,0xc10031400011830c18d1,0x50c30401a3670030430,0x438e8031ca0431850430,0x30c11c90c30430030011,0x61c50010c30c3063cd00,0x30c30c59010324300314],
[0x4280000000000001c714,0x4100000004004106,0x90b80000,0x242f040000000000,0x1041001040041041000,0x104100000004000090e,0x10400000243d0000010,0x81910000400000000000,4194304,547636224,0x429120000000000,0x44b00000000000000000,0x1842c90071041881062e,0x1ce2c624a10a92b87108,0x3461e54138634f108304,0xc000000628f3852ce109,0x100004000000000096c,0x40001000025b50000000,0x96f000010400410010,0x10410000000410,0x1000001000025c100,0x1000970c000000000,0x5c504000000000000000,0x100000004000000002],
[0x4000097200001,0x25d1042043000001,0x40040041000000040000,2421,0x25d50000000,0x975400000000000000,0,2479360,0x9754000000000,0x5d500000000000000000,2,0x97540000,0xc20a5d5000000000000,0x420c0082083081102002,0xc108208008208000097d,0x20420820260a0800420,0xc0988c00c20000c20c30,0x10800c30000020020000,0x830000010830263300,0x39920208300108,0x65000000000000000308,0x4000004002,0xc000000000099480000,0x2657000000000002],
[0x80000000040000001001,0x40000001000000040996,0x265d0000000,0x3998010000000800000,0,0x61a66300,0x8299bc000000000,0x67300000000000000000,0x2071492071c51871c71a,0x1069b7c7186,0xc20e6e9000000000000,0x420c20840840c4041082,1059268,0xc20c30c30e7170000000,0xc29d0820810c30c30c30,0x20830c20830c10420830,0x30c20840c30810e76504,0x20420c29e3c30c30820c,0x7b20430820830c408204,0x430c30c20030c30820a,0xc30c20820c29f603083,0x27ec000000000000,0,0x10410000010010419fb],
[0x27f30000000,0x9fd810000000400010,0x10400400410410400000,0x1040000001041027ff04,0x1000000a024004104104,0x80e04100000000100004,0x104200000102,0xa04c0000,0x4206813000000000000,0x80000000000000042082,2567,0x810820830e81e0000000,0xa0c400000400400800,0,0x31491c00c30000283100,0x30c60c3a1a050c60c314,0x8b51870c91c31430c61c,0x1861851851861891861a,0x2452461c6248a4443145,0x1c31a97d0c71c6188147,0x47209245187209205189,0xc7148143146208187a7b,0x322a542071c61,0x41a97c00000000000000],
[0x10810420410810410410,0x104104104108106a7308,0x2082041aa10104104104,0xa9c04108104208108204,0x810420820820820820a,0x81042082042aae41082,0x820aad5082082042082,0x42082042082082041081,273084,0x20c30eaf40000000,0xabfc00000000000000,0,2817792,0xabfc000000000,0xaff00000000000000000,2,0xabfc0000,0xc50eaff000000000000,0x40000000082103085105,2761,0x2b250000000,0xac9400000000000000,0,2827520],
[0xac94000000000,0xb2500000000000000000,2,0x81081041ac940000,0x2b2e000000000001,0x80000000000000000000,2763,0x2b2e0000000,0xacb800000000000000,0,2829824,0xacb8000000000,0xb2e00000000000000000,0x4200000102,0xacc80000,0x2b32000000000000,0x80000000000000000000,2764,0x2b320000000,0xacc800000000000000,0,2830848,0xacc8000000000,0xb3200000000000000000],
[2,0xacc80000,0x2b32000000000000,0xc0000000000000040000,2764,0x2b330000000,0xaccc00000000000000,0,2831104,0xaccc000000000,0xb3300000000000000000,2,0xaccc0000,0x2b33000000000000,0xc0000000000000000000,2764,0xca24728302b330000000,0xc0ae3c400000740a3400,0,0x900700710f1c002b9200,0xc9af70000000940,0xbe800000000000000000,0x18e0022c034f20902,0xb0e80100]]

def tile4 : List (List Nat) :=
[[0x3904ac3a000000000000,0x8f48c38411840e400113,0x21c01c0000b42,0xd00749536d262040000,0xb7c9334d30e0133cf3,0xc0040000000001c80000,0x22d538c24341146e1510,0x4000000bb14038f1c72c,0xef42d228400000000000,0x3c728001244740e10e5a,0x31090c2be6001cd,0xc056ff631148c188000,0xc001144335101354844d,0xc3000000000347084c27,0x8f44f4031f1075113521,0x40c67c000050918f2034,0x154b20600000000000d2,0xa28300260f3c0031f401,0x34ac9b841020cb4c,0x28900000000000010000,0x104104004104104003,0x40ca4c1000,0x4003294000000000000,0x1041001001041],
[7335,0x400410410329d0000000,0xca9800400000410010,0,0x2041040001041072a600,0xcad4104104104,0x2b604000000000000000,0x4100204104100104207,0x40000000cb181041,0x41072c9041000000000,0x80081041040042042041,68719479990,0x410400010b2dc0010000,0x40cba800420410400020,0x10410410000000010000,0x10010410410000b2f204,0x41040cbf8000104104,0x30704204100100000000,0x4100104108104104107,0x1040cc500000,0x400331b001041041000,0xc1040042041041000041,265417,0xd124b244033280000000],
[0xce40000024c3042801,1,0xb34800b3102890339400,0x203d044310000e38,0x41c00000000000000000,0x38e20924235024b23,0xd2340000,0x30a27490003000000000,0x93030802d54cb2c20cd,0x8000000008d49,0x8b20338e2754e2cb1000,0xd7d4444b20010e4962,0x30000000000000000000,0x45038b203188335fb0c,0xd9f0028a1c700,0x68e0ca08300000000000,0x2422830114cb24b0862f,0xdc38010e,0x34a3b7351c82c80c2000,0xc30053c62cc006503392,0x89000000000003000df2,0x8d58e4801f80a2ce30c0,0x3e280800028d34e1003,0xa2082c22000000000043],
[0xf3100c734a312138ea20,0x4000100e608720300c30,0x98e00000000000000010,0x4104000000204004103,0xe6580000,0x4103996000000000000,0xc0040001041041002042,265832,0x41041039a40000000,0xe6a800000000400400,0x10000000000000000000,0x2041040042041079ab00,0x1e6e8104004004,0x9bf04104000000000100,0x4004108204104004103,0xe7381080,0x79cf040000000000,0x40041041000041041001,3702,0x81001040079db0010010,0xe79800010400400020,0x10410410000000000000,0x1001080041041079ec04,0x1000e7e8100104104],
[0xa0100204200100000000,0x4204104004108208007,0x41e8441000,0x8207a18040001041040,0x41040001042042001041,265866,0x442041c303a2a0000000,0xc5ea48718a2491872462,0xc1ca2051841460002041,0x1030c324730a2baf224,0x82c60c2ed48320a1c700,0xb910c018200008010724,0x40062c300824a1c92b,0x1c72440072c9efa08080,0x820bc3b10420a0c0000,0x80205286000003246180,0x206283082180080f1d,0x18524003cb120a0800,0x6f36c61c70000000800,0x1490c00000002c40000,0x2880000000041fd0100,0x4000102f478000000000,0xd4e0000000001c82471c,0x8104108204000004003],
[0x40042f5782042,0x8107d6b042081041040,0x80082042000000000082,0x42081081000f5e,0x108100107d830000000,0x80f63800000010020800,0x820000000810800010,0x4000000003d9a00,0xf68c008208200,0xdab08100000008108000,2129923,0x81000001f6c41040,0x103db8000081000000,0x40000000000082000000,0x82082041000000f6f,0x280c4900309c00000000,0xbf68a089700887a630a2,0x213f68220a701fe93aca,0x744f7f68a08970093164,0x492f5de9682309702ad7,0xd06ace692ea8a088707a,0x21418386aa889620c805,0xc804904438664890c060,0x34070d8641c7aaec400],
[0x955135f4ba40400c85c0,0x2c99a42175f4aca2eed6,0x900013252006b5fc6ad3,0x2271aaee8e56e08faaf6,0x200c8a400eb861b9e265,0x9feb22aeaffe93f5ffc0,0xea23e62ed2309d6ee51c,0x4e5c9bfffa40400c85c0,0x862de5ad18ecb5e9108,0x200b28042001ec95b5e4,0x2b09332d09eaf119e777,0x680c04703ca9488267b1,0x505d80b401a80fd64990,0x4ac01980f9251078081a,0xaba30202079806852250,0x4ce00401078801c200,0x2cd970060401380a823a,0x255230241101783c3040,0x900b0a3001602c02a807,0x178193803101cb524c0,0xb04604d11810130808,0x600b480301405c002102,0xe004a5dc90704404101d,0xdeabf20061c04f01417],
[0x1a0b056008819080968,0xe1800148001007000204,0x2e1d0038e405300a5d2,0x6608c809580f5e97a0a0,0x272ff0561c17b0058b45,0x1a04d1582621e0288407,0x20480ffe4f40401c4320,0x78cd30a4131b3010097d,0x203f7d27c46730ff012,0x1c0e19c62068c2c038e,0x400080dba57056df9250,0x1080079341e07047009,0x16bffe8016bb50200b12,0x602a1061d41d012022a0,0xf0b881e925d4ad400012,0x33106096906caa797f40,0x881af67ab1011000a003,0xc6161ec0a2942d602e47,0x88999f1411090a00190,0x1e6338520043c5407e10,0x812370804b9290060511,0x4a02988a0319c08b80ef,0x25b99db300aca90000e,0xb00cd40a36303a80b0a6],
[0x2821640f5aeab0a00acb,0x58c000a004a2616a0750,0x1ec7981484f03febaeb1,0xc180b040e01b834640a8,0xcc7ef03a58c302b48b7,0x1007e4d801507822d15c,0x881820500c80e9014c90,0xb000ea03c603c4198ce4,0x81635403356f5b172700,0xa00052c5500dc1ac4c18,0x718d849020202c81faef,0xb0c40ffdbaf180205020,0x15d00231f0660547fc05,0x81da14f815e422f03010,0x4719f00078260c1b01fc,0x1c0203468c0de89aa000,0x2b921011a32c0c2a6030,0xe8240780dd8026823c60,0x92069adbd80b92300198,0x4ae9e0dc090b86e81e40,0x1fa81ca12a07f67e8001,0x55ac0220029a4cb86ac8,0xa1de07a108903fd2fac0,0xc00c65201895cdb08604],
[0x81eca8314ab07d52fe81,0x482e0c918ba1c60767f1,0xa307c99280012c616000,0x2c670340043df202c149,0x7ec25b3e4820b14678b4,0xec90085901c84078c1f2,0x81ee00c70b7c0ee4b814,0x444ffaac002adf019b3,0x113a360ab81b43ca04b8,0x193057daf480002aa220,0x739b0d2be02c3c607cc6,0x182bed7eb1200c5de026,0x812046a16c81ae2263d4,0x5c20004087012b8183ec,0xd40f47fe12775fc2011c,0x1f0ad1e04ca0ed0230ff,0x1de19748970862f93f0,0x39243510b018131e031b,0xa007269970017d00c580,0x1e511a0e5a011c053cab,0x53ffe8014da61e005f4,0xcb9a0f7f601c3e90155,0x87c21675fea974900220,0x7462a640bc81a43dc01],
[0xf23dc59fffe8d47c3460,0xb6e021659ac0751f3034,0xce6aabf6a04e486003e1,0x3808111805c0189280f,0x2a08c230680b93502b57,0x4b6054dc02e026216034,0x1e22420070b92700b52,0x1ed4c04300f598131a2,0x82d82177e009073466,0x622f0b80413b280ac550,0xe8011222846322baa02c,0x565803c0d81456f747be,0xb059c05c001dc02e02a8,0x3d700470246580640340,0x531824e80040ac58ac1b,0x180b69e5fad2903ce304,0x186090d8559301f0108,0x5ac04401bd00a2ce40a4,0x2040db5d7abe3016c033,0xdaf0024898291b501637,0x38a33c32018284bb580a,0xa04016da908061de40,0xb5702df62b0601e0500e,0xc0b008f19204cabac80a],
[0x9003045ca24414858c00,0xd40342e0b0a8f02dbec5,0xe000ca2232907887f1,0x512860410832968096f0,0x2888a23052b186216402,0x856a7b78100bd0aa03,0x5a04a02e433b00102c17,0xb288100600482e572433,0x80324c00c0830ee00d40,0x3230181004f00d2f0000,0x709cd290790e3c061068,0xd0b41717eb6fbad26001,0x40c5e70f3d0a80b063a0,0xb75f60500e60044db89d,0xf901719e79b063821c3d,0x8a470a040a5e5041662b,0xc09120296031c1d81655,0xff405182070308835a9,0x4c60880c5451022025d,0xc052227e00380f70311a,0xc4781a0d409a80249c9,0x802afa8198c4a01c487,0xfd8ab77001c4e8013648,0x42cc203c1105390c46ba],
[0x30101407d0015193c0d5,0x447e3930801c0590db5,0xc0405020201965411c82,0x815ac2ae80a922540d9c,0xec1005c19c46c010a8b6,0x7009403656052c50781a,0xa00b881c070308085070,0xc30ac203af08012817,0x20326cb0200ab67019a6,0x8407b001651636703210,0xe6158063302f868b762d,0x3020e003a80ab0980ef0,0x2e251c1a0a6a1b29c0ae,0x8c860211101a017904e0,0x2a15b62000140970008a,0x306648c012c814650948,0x1329c1c070358519062,0x4ac35dae281458b1013a,0x812b570260370142019,0x3be81c86a0f403326d50,0x44c0403b0a20011250c1,0xe28133da0d123b608874,0x2d2071029524a7281603,0x3c6c80431c7976eba030],
[0xa9894069ebc38893819d,0x5024a06431735029b134,0xb583692128981adcc040,0xc6f812672a633015a0c0,0xc000396000a13060d0f4,0x3f8520af3b22e0725280,0x450911e58c140a8ca0,0x1b9b3e401c4120c0528,0x30ec12326cbaf812bb10,0x20014281386602283541,0x595d80425d3ec0403acd,0x4a3d004fd3c169eb7008,0xc060202c2077015310c6,0xe14cffc6a73890f03676,0xec20244e289291c0509f,0x2f058d9cc040402da004,0x7c05608299691d989e5d,0x4e116ca08b404caeb825,0x43607a11410010396000,0x871644249809e0e83044,0x2c82cb8c0c992906194b,0x194aeb95bad788c8058,0x72b3300a0a819be00c25,0x80c707c04806326eb015],
[0xc0a0201960004739423a,0xb888754e22081a069ed4,0x402ca00d4490810b7301,0xf335dc67e04cdadcc040,0x181cb51298214480fc82,0x3934c0c72338e01a2c22,0x398f0a9014901126a1d0,0x5440041f500d5c2498f8,0x4208b901b0f41f0112c,0x60003c02b01641b08701,0x66daf8fb00906184607e,0x41edc01103ca8f23c6f0,0xd015c0341d18094142c2,0xaebd2808f03a40f1bc9,0x138a25684b8e80f640aa,0x9a4a02b811831e8060,0xaf0032002e0006014aec,0x65401103bd2f0bc4d004,0xc5f038b03c518216f210,0x65a70e82a13807894f0b,0x5071c0240a3c380e1473,0x85e0d490f80523025494,0x201caec240680f05c09,0xbe7004af04af49802e00],
[0xcb1ec0a240110329ef03,0xfbc170788205601e033d,0xf9c7c1af0600781894e,0x109410060813838d0191,0x1fc0cc0b0a022405a180,0xbe0b280006014ae43010,0x7aa0a54804af00018052,0x61f00502a130210a00b,0x801e07bbca53bb5001c8,0xc3f0589162e7243a0e37,0x1f2a4820a0036e038384,0x9a1061b835e6be00781f,0xf12003d4078788291132,0xbeb4ae0095fe0e01caf1,0xd0012fac0a8270286c0e,0x6757014aaec1806014ae,0x250072bed606e0ae03,0x781eed296a51e00052ba,0x116ae8a324db82a27a00,0x6001cd405082a906934a,0xbf9e4e00781ea8296a55,0x1292107da524160c41a4,0x675b6000bf54e0610264,0xd6d57e4201c6f306e280]]

def tile5 : List (List Nat) :=
[[0xfa8980e2205261201405,0x96ac1806014af1000e0,0x26812419c407d38f80b,0x21010c07b40018052bb8,0x5a9e900052ba04200ec0,0xa533178a73802202baea,0xea592001904481a2c804,0x19981d501400f016a7ba,0xf04441e582984a18d3e,0x86741e65aa46a0e0a474,0xc49050ba0744f2fdc06,0xa01cae900e83c301b036,0xeb014caf20343dd0538,0x11cae400e28052be02f4,0x404380a9ca5baa103007,0x600ca078be05944cda00,0x9815f480440ea73aaa58,0x9c4a0920462b0186dcda,0xbc07aa22517f101c8680,0xb0f5e02f01c5c03406bd,0x1aae05c12a0596c014ae,0x72be806a40841b605b0,0xac00e8021101ea82250,0x809d8026080401cafcdc],
[0x22111a01d2ba98a57810,0xa4a98a50604281b60524,0x88cc411b40f9bf00781e,0x6a207830262f04080430,0x114aa401405816012a2a,0xdc8518886210dac1101f,0x625006a6c200f2a0560,0xd80380e67deb5ad703c7,0x11a08b03ac481b41de20,0xf58b007072fc8601cae0,0x3c481ec0040410198d2,0x348065036c2018052ba8,0xea48600052ba00d801c0,0x888e03e22f00f016a6a9,0x41910703a1b0850e094d,0x20a6961ea6b8aa7ca01b,0x8e1094a544013fa8d702,0x60176104980b486e3352,0xb3ff08c1b38601804a7c,0x381e58080868f01c9af2,0x806010e008c0eaba1030,0xc057b9af6b84e059c32b,0x14aef057a50468199067,0x87780511dc3903858e20],
[0x7001b2ba0ec0e1063c05,0x634db5c0110329ca5292,0xca4820009809238050f2,0x3688f01a68660d1ea529,0x1107c2a0520e2862239,0xcd3102e31ea60c0a7160,0x26c06c1a38462640572e,0x11a980100790045034b8,0x6d42c2c36e0388e9f83,0xcace2caef0025815c132,0x4f80983cc064f050149,0xc4804a894e3cae5001cd,0x4afc0a60638177800300,0xd8055028600440200801,0x721a4068170120d656d5,0x57c1307e02d5e7d6b833,0xc09f01700063e3080150,0x18502281e7d256c8010a,0x483e074b4d5a1001043e,0xb66863a8011e874e0d1a,0x501ada80043265d818c0,0xd6e88a0490145434140b,0x88b11c1c181a1081e7cf,0xf40944091e8070006363],
[0x399f5a501406e03815b9,0x48052358705502c2dc0f,0x51181cb86205d0dee063,0xc1822150f8d9f8e7006,0xbd3de368004e48640f97,0xa6604420861c80d171e3,0x4833072d5b9e300b301a,0xf7b9f5af01b287074c1,0x683e8709e68a38d16806,0xf0bc68f8f9f8c9000c4,0x8d8e1004238240fe090a,0xa992035e824ccd818f99,0xe7d805118057b5b9fc01,0x63f8063071e01303ded6,0x58360560e3bf0343e7e3,0x99828d05920af78f8c30,0xf01795b9f411c580e050,0xa506e40941c767d6b831,0x4808c80883e7e1e33801,0x700a05828d5e619800e0,0xc410c0a314e319584503,0xc0db56e7a814140d0210,0x755b9eb03c0810c82617,0x303429be0fd04f60b41f],
[0x21a07f40e1b40b9f7b74,0xcd081c3dd67e20a00504,0x1271720f8aa8d0450d59,0x44424044000588501982,0x54004d9894f8cd872413,0x14538347615b9ed00358,0x61787009142e0ea90f2e,0x420d4604c305a0410f9f,0x249438d43c2f9f8182f0,0xf798182f073720dc5e8,0x161f41ce46c141049116,0x4e1302b819d5f609807,0x9483ec0d756e7980053,0x282d08a033d767db4805,0xe054a541e2d767de6805,0xb4c8594f9f6d79901203,0x4837408c02048983292a,0x36dc0cbc1c2320db67de,0xe60006706b00cc0d7c4,0xd102a57d14e7ffb17000,0x202007400b652c5fffff,0xed20ab7fff9fff2135c6,0x84002446ecbf5ac9aff,0x9331ffeffffd2486a020],
[0xe005bef70ffebd7aaae4,0xec505f42550861080800,0xec8182015051c29c1fd7,0x3e000a175b1096db312,0x22dc9bd555556bf2040c,0xfc021402600c89a85cce,0x19daaa5284faa4b2edb7,0x62ae6db6ee008901d009,0x5409400c4c15648236a3,0x9009850c4c031259c00c,0x42614805896959fb1a44,0x8c46514613a80145488f,0x4620f85b6b9ece21f803,0xe331158600c832659f32,0x230faf9802a121009c04,0xa61d063cbc3c03c18cf1,0x62833650422d93bd800,0x81b01950c28f130f5cd8,0xa9652cf175ddf65350,0xea1028b8d7d71b1e4230,0x1142b01871185624fc4b,0x80900118c31a393aa250,0x50350408287f6b9450,0xa610c82c2386876bd431],
[0x60fe03fbe61fe288525f,0x63e42067e415006be403,0xec58205fec682063ec20,0xec2053e42057e448205b,0x8e00f23d18204fec3a4f,0x342043cc05007a04001e,0x2037c4000ef62c203fcc,0x2fcc142033cc242033cc,0xee03a746132503c40c20,0xa401c017a4001d360007,0x3ee004013a400c283,0x284200ea0020ee0002ee,0x88290e4001008a8b034,0xc1688c0a7c0318d2a829,0x87880248dc920a272801,0x2651620941880a6c8660,0x840974004f0a9c002698,0x202d41a0c000a8c3c18,0x302c1e1810823a5ca844,0x87880ca209cc00301826,0x16a1219808803182660,0x188409741b452a09a518,0xe090c0e09023e2c0ac8,0x8603c0110222824098c],
[0x74265162086508622808,0x876c0316482402e19a49,0xa8e40c864c3a877c08,0xad5381f802e65424fb5c,0x4000b200ff59281e81f,0xed6b7e955528ad4a5fe4,0xcfff2afdd854000a2006,0x885d076a2c01a909c47a,0xdb58ffa228336083011e,0xe228066db53881d23814,0x2896ef1d4800cdb51c7a,0x637c003b1e02fa8e08c5,0xbf2801961df8740a48df,0xa6a654df81c86db18481,0x33c0606db08f03da806,0x9c3c38a066dc0f0c8044,0xa6d984c56e3836c30103,0x8347181d195318c56c88,0x3867086801d4038c1a31,0xd1cd001251c1a318347,0x69018406f44c9696e8c6,0x8288508134001c020240,0x204c835838838915c15,0xdcc50712905688b06a20],
[0x314204d81c278892e134,0xa42030b4070903bb0825,0x68591706506042380660,0x82a81b12426d813040c2,0x1004fc7b0800a830f081,0x65a11004fa78d833ca01,0xc4b7d3c4043002492d40,0xe8f375380133e69c0384,0x9013b1c410612237e039,0x39db7c00a83f3ce805a1,0xb6db79a830913203c201,0x49a80265783a759d0804,0x4b2804d03d3486f009c2,0x445e0d99310ba01684b6,0xd425700504b6930c0430,0x6900b574bb0148147605,0xfd540135d00d77101cc6,0xb2a00450002313024f66,0x4701f29d110804104b5,0x111e4c20b80d84b4faa0,0x1a0160b02a7c04100158,0x3d004d4a994d0801e234,0xef00c184b4e248051001,0x2480510162881f164d2],
[0x6103665b17b600c3d20,0xd8d7bcc0db4b21c0470,0xb85ea074fa8045d80394,0x1ed804c80e8201483dc0,0x12184021b80490010807,0xe404100625014eb26998,0xd2102580f929d8111021,0x782501115a8b503021c8,0x50123e940108086b0158,0x2a11100c6c1656014805,0x629302b2795804b008a0,0xb220109c90481e80fe2a,0x4500045301a5564c280,0xce03b84ce10210b02114,0xceb60462b1f8f8045000,0x48c748437016805ac07,0xb8bc045000308500e116,0x4690538088e657a0e2b1,0x17603a56885e42b178b8,0x31b5263162b1187004f0,0xf142b0e87004b04a4c07,0xa40aff0138886ac0788e,0x7220f9017812428c6f80,0x3033b004100161f5f7c0],
[0x10f20138420cbe22ec07,0xe77468053c190a840340,0x1081c36241d4ef405d6,0xa016801713a014410e1,0xc01486a0e4d32a40640,0xac5001903a8c4680241c,0x3806e41b5f8b01b93b5d,0x1380128dfc06da51401,0x4f0e41a35500a458ec6,0x2556bb4bc03851b5cb1c,0x4701b8bb017e900a07c0,0x849804501e0581bcfaa2,0x101140f327c1100cd1b0,0x2cc05a8f3100c002b404,0x14308c80262ea301587c,0xc090c850013090084248,0x20042c04700535bd8b5a,0x1882012803e9ed7381a3,0x2c7e01387d01c5f0250d,0x1681013800952c0272c4,0xf481388845203aa010c4,0x49d40450004a008cca04,0x5c05e0322aa2b0150439,0x6e01782ec0f13b1ac0],
[0x58110128098f2a071040,0x2a09601746b40c281301,0x208a954540d87960d010,0xbc532997004b0040804,0x15804109101552772a4,0x4d0785d01b1fa607820,0x4068c286022ad0b240f4,0x36807e110108038e0c1d,0x102c81131af8028bf00a,0x821c31c0b40470067dcd,0xc4041002e13e009f4212,0xd00b84008e961070d120,0x301aa7f328a121380004,0xb0cf889400cf88801e7f,0x505022082b817c078802,0x280b60238010ec0bf00b,0xe84b01b401e04f32b022,0x806143cc224800402080,0x28007018a6019024483a,0x31037c04204c09dcee22,0x81400013d802a07c01e0,0x18405c0d805600908100,0xa805b8029213886c0a1a,0x3c020d60013bce218800],
[0x1102b4f38874023c05e0,0x4406cbce21d807a00ac0,0x20360880c04084a03b80,0xa01e4033088613e87a0f,0x8afc53601303260f0507,0x370022805c11028821,0x213aac0085008508401a,0x3338215805b809d8026c,0x41c483b01f4000803c09,0x933aa21480380280901,0x80b81082e0d0eb01703c,0x7d0020029c84bc024811,0x34130882cbc800200300,0x705a07d0021982440460,0x37031620012a5e20b802,0x2b2e20880d07a0743170,0x20b82700a1a01500340f,0xb8710141a80340f123c,0xf104a20c8014803a06e,0x204101212812140c07e0,0xd003a60480643322020e,0x717409a80242ec081409,0x12080c093004093b8804,0x28b0805001840d980242],
[0x20083d02a050ce0120b3,0x3c0950360730301400,0x11986d03220004087e12,0x8800e05b00c201af007e,0x1f00cc0211b2a1fa801,0x32ec121f98030218806e,0xa1fe0437801a00c60038,0x6a00860461f9800d20a,0x7c5006f00101d00d80f8,0xa00858d3010c1b2a1f8,0xccb6aa0e660bc02c02e0,0x449000ed84470012487,0x5b0243781c4090b40490,0xca361f044900700a063,0x143c1d002038b0f802a0,0x2c1f0454008730740a32,0x4cb07c500e80f80b5803,0x286c2411034330138184,0x22ede8c0c0bc08901d80,0xc06301a1222c07906113,0x910023a10b224094096,0xbc0ca06a0596cef84350,0x8240a0306246827e0d40,0x10b8241f028081023e17],
[0x811407411c06100003be,0x1087ac888003071482d,0x1eb8b602700c805804e0,0x848034005a00182c8bbe,0x81008422987ac0150a2,0x14023004100b27280794,0x40d03c81cd880326c0a4,0xe60388201a80580b1e8,0x8e24a440703c0cfc05,0x32023803b049ee93274,0x500158089000a410078c,0x5a0170250020b261e4ee,0xa044800808a032121c28,0x6e03b8210006c6a80100,0x100001db1bc58c07701,0x6993a950051008201e20,0xe05e0582d000c04429c9,0xd8241030cc6066580302,0xe0ec06c860083e302220,0x2760541b02e00501580,0xb40c83ec6ba91000a619,0x410a0243850b402400c0,0xfb81a0b5891e2280613,0x58482a01f0128000076],
[0x8a321ba85008801e0028,0x9e09c0882c1dc06e1f0,0x8d074c7e1e0940c0c0e4,0x910e03e01d000e5a800,0x80ae583cb06348096076,0x4024012033806408c145,0x3c28075401071abe0511,0xb968683c9007018d00a0,0xd805848f409088760cc1,0x70d82d0082c12394ba00,0x14ba07380c8742811da,0x9802fc1c83a40aa0f04b,0x904780c861cba0c43808,0x1403a003a0502f41de01,0xdc09800804e01b01a108,0x8000e86004a4291cc1,0x1b02701c18087e0a4088,0xb71e0712838480a3c270,0xb08724e3a01049f12119,0x851b8004028ea028bb01,0x4190400072e82802a124,0x3141c2033e0030073009,0x839ac507140123c8a89e,0x44b9b10038e01c40d]]

def tile6 : List (List Nat) :=
[[0x940b8480409c0e205c1,0x1002cf8e26716405580a,0x47a07204e04900044839,0xdc4cb41b804280b00180,0xa0642c5070e6c8310be0,0x8600682468807c0981c9,0xa04700fc04a05c3608ac,0x394c58819e81480140f,0x6801d400680320643200,0xc0088a0310320c5c8ee5,0x160db803200c2846b034,0x3080350342e41782e53,0x40c8151641b940dc2076,0xd08602890e0438f4130e,0x5550ac8bc14841628a28,0x1b83690f9e83e904378,0x400871e80c5602601100,0x94f022c1d06d0181f817,0x301a1d02701ac183641b,0x26cc3450a0c47701904,0x202e8140006ce02806ce,0x66606ce068027a02a80d,0xd40e40a550070678098,0x42180bc121034e018fa],
[0x40d0041b280101006c12,0x1102a00500a203305e80,0xe1fc0884e0c1b034e078,0xade6044e011030180440,0xcd003201ab78400c806,0x4900ff00b603788706b4,0x6ade380450019cde06a4,0xc028e204180a41104360,0x2301201032de2800882d,0x8dea068dea62064177c0,0x482638f2ded806801206,0xec0920260fc090b07901,0xac142020c068ded801e0,0xb800910c8074009015c0,0xe00b030be02605a868de,0x690030dbc85c0127700c,0xb8002edb86640c403180,0x86900e7001982edb8807,0x8c0858002e19b6fc3783,0x106021982e0158130a41,0x3c0182506207700182a,0x20808c0a58c84db9832,0xe0b0c19c84db9877013c,0x18064dca039016407f02],
[0x1540687e057003502c19,0x66193734372012020b30,0xb372191809f805f80781,0x7802101bc02c15057000,0xa064161b66553729002,0xc04e502618c01607e0,0xd99c018e036734e022,0x48208170940f5b660ab8,0x1367c01782306a0b501,0xa800db000409e025002a,0x82458503601a0bc0ccd9,0x460c840ab6610021007,0x88382600fc0242c28c6,0x8217200b6ab7060c0f08,0x184d000a36a18184ec1,0xa9dc5728260041520204,0x24800b80d81680c8242d,0xf417815013808da829f0,0x60c22f814a40a07804c0,0x6a9002216020604877cb,0x1a0c6b0320a299136b73,0x220a803813602180185,0x6008c02480021cc0a18,0xe817b8360732006c0fe0],
[0xb402a01580ba047032e2,0x33c019017827c241081,0xb60178263000a837020c,0x338881080780902205c0,0x249826d8380198383c60,0x740653002802300a40f8,0x5603404dabcd8026d001,0x15028dc0640740960210,0xd905caf60e832c52a018,0x2d0594031685caf0800,0x30806e13c1728027035,0xf08c15401a02900e4027,0x43876064061abc32364,0x380c541618c2f809500a,0x2a054d9000091a006a4,0x100a014008f40e261a2d,0x18a82c1791f84846640,0xc82a0d916d902530ef05,0x80540270090f05094150,0xe60604060704c389834d,0xc2b135616c800b105b4,0x88341460312600440f60,0x68093002200a024b5616,0x320c81132d5822709201],
[0x302900c0c8070707201c,0x8b579000f82950580b01,0x7006121208ac042385a0,0x3d07441c2111a08a0189,0x81e04b000d5823f002d8,0x1d8061c406412120910c,0xc0a10c09010b73a0e318,0x9142b5ac00a5058d6e54,0xd69741608005a01ac00,0x167804b010e01501b006,0x5880160d0b01e0695b5a,0x50081602070620dc560,0x4702c19805070c8686e,0x585000383982c3e002,0x3414283058128010d204,0x2e0c4e02601604700840,0x700512406c0adb5a0828,0x34b4d8564013404f801,0x2805c8029b3a34bc0e50,0x6020788e15a800701a05,0xf802613808809c03d00f,0xb8060380f81e2ad856d2,0x1000c1c1981c51802100,0x801c0f0c82e081e3eb4a],
[0x1f300389070320a4c05a,0xc08106285a071000d28,0x203411409592200ac0,0xb40054072a0400490b,0x7900a405c00034e0718,0xa081ca834e1001120738,0x2340d636047802302b02,0x2a00ee008c1534f4010c,0x2101a0540034e073a060,0x2303f0021707120923c3,0x240453587025269705d0,0xd381c500af6042830a8,0x2900882412e158288100,0xa8cc022400c1c4066028,0x6b52a338017815010806,0x9500720116032058180,0x6a0c416214ce6a33803,0x1633a448d4f807fc02a8,0x20138a017404c3506432,0x24048185230353300041,0x40c824802600a0f0b1a1,0x206a606887a04848384c,0x830cb0618a101e0c0000,0x99050178120900380281],
[0xc325851907419955c3b4,0x7028c0c0740020182e1c,0xc048a0006c0030001e08,0x4070080a06c000701,0x400c80929006402581a,0xc80140006400c8090060,0x190020281e0007000700,0x70072681e00681a00,0x7000700901a2080a064,0x20281e027a801e000700,0x81a02881a0007000700,0xa81e0020281e02a80200,0x2a000b600b8180e0002,0x74608060ac00001a0007,0x74000703b0642aeb00,0x28000c406405c8320b00,0x20110002019803081a02,0x20640218042000640526,0x27704502f8180082c4c,0xa060bc000703332a0007,0x3281e0007000745036c,0xa800070348006e4e2400,0xa06408d014b011000201,0x2a0400e407c03380000],
[0x816c002e007400070412,0x48208060ac0003000705,0x7400070007400ec06401,0x3e0201e220520400fc0,0xd818060007058020006c,0x20807404181c26010703,0x7307000200074290320,0x1e04801a0474781e00,0x19803e03220206c0468,0x8001e01c6c0ea060080,0x202e2503c831a0207c00,0x4080a400050000120000,0x5812cc062100e05420,0x4080a400f0204080ac,0x10202e0a0040a0840270,0x801200781202601200,0x80a40098120005009812,0x4080ac00102826160040,0x50010202e01b81200,0x298c0160000a8160005,0xa08c0290c8160010202e,0x40ac000500fab2542040,0x56c23cac05c02d02080,0x7402e01202d1201600ad],
[0x340480804408e040004b,0xc900c900506080a054,0x70110002010840008044,0xd90ec06824e020543704,0x118a32a8000da04c00,0x281280c419c06200054,0xa0808102980e20574182,0x2e608040ac00eb1a4123,0x13aa2ea02044000010,0x3c0801c01203c81200f1,0x1b820160afc0af01b81,0x3f81203380440800054,0x5401dc00004fec040812,0xc000800160fe060a080,0x51310c00c0d0112051,0x402602040310c004110,0x1802000440028002048,0x3554e040c058020005c,0x5d35183003a194521494,0xce54ce64801ed561c2c,0x9b98fdd0e98f0061152,0x35bdac9ccf98d00144d1,0xa5e4279c0009810026b,0xa0e0237462203c07829],
[0x6c146508484d8018036f,0x884eb642382300805d10,0xb8a479c5c40bd001c19f,0xa800d001445592a6244a,0x1884985252d623120a3,0x9a4d590851a604a364f4,0x225259388034d96b400,0x50a01c5744ceeb4c1a8,0x48c40c110210ca8c053a,0x233a6db634c1b0f5e64,0xc20241825a6cd70c4acc,0x26d56150943274b081d,0x130b41ba2008f02e14c,0x3b443592045de318108f,0xa7180088a1e06e981303,0xcc628fa01802c5c10201,0x58827a41862000cf60d,0x280241328ea07c206964,0x6c940116de339488f76c,0x2a01b4de028496230509,0xa953981909e6041be212,0x8430634fbe180d1b98,0xc3122819c081a1c852c,0x38646820670c197a0b62],
[0x3c03ba08f04cb2f4010d,0x932402f9d60118104793,0x504dcac14cd5f340306,0x706aae40c8e1c875c03,0x5dcd400882086155c88,0x1174dc981825e4cc1105,0x8d332c661c6593880308,0x61140914670c14420340,0xc440a5a2b0cca048d80,0x10c4092704b15c311302,0x802d8c2101c83e156220,0x20a5e13b5089897a8e3,0x4e4c07081d040d0a34c4,0x30ea440f318e09024484,0x332054a03030a010e01,0xe4a004e124a4a004e05,0xc608001a760332120301,0x1d81c0a6c014418d001,0x4a1028562e521d0996de,0x3e04003e98020104131c,0x9c2e0b0e2088a40d0702,0x381e006c241a0222350c,0x10b0904821705001206,0x420c21c406a60d038209],
[0x44003942070919010905,0xc4270335d1c44f0290e5,0x34270140eccc270145d1,0x6401346a00bd32723956,0x2c5b02de41a44b0268db,0x491b62354e781d02d8d5,0x462e4c0661900313a4f,0xb4a4172a5501aa217401,0x8c524101412a590380,0xe093cc0170521500291a,0x844a5c250e13018f81,0x4110070420080488424,0x81f0001f10c5d0299f1,0x263a07a1cd28dd007c42,0xc39c81a073b402c121a3,0x1073a43a683e3a683e03,0x378c18de0018c2af1102,0x5614b1801a02a00acda,0x5434160b405c5868415,0x9a2642e5814ce0b1c2a,0xbece50260010bace10a6,0x32544d00ac406481ce10,0x30221506c740b034200,0x1200f8120b009032a448],
[0x8638bc090053c8080128,0x82ad0250226c21281600,0x440ebed80e01200a0008,0x1b1103401000c81e496,0x40f0141b011f4240409,0x11111113151517171717,0xb0b0b0d0f0f0f0f0111,0x96050192030709090b,0xe8279c959862010e0096,0x2723a1ec03418c1c06c0,0x1c2615082721e3a401f0,0x2b00701c3840dd5c0d8,0xa36c0269b94e270381c4,0xb8050346dc0500e806e1,0x781061b0d2806c29880,0xe401b0d0662414941414,0xb40164e33405700966a4,0xc688ec01a858ce0680d0,0xb0289a0c132803a02604,0x19982683014409464123,0x44bc160b090a02a012c0,0x62e1247c030620a402ea,0x40a290220b84a8024806,0x8120a2190b684381c383],
[0xc11c0145438470a20f09,0xc82642c1040080706642,0xe1226192090841b4118a,0x3e28240841918a838803,0x163472846028300188a8,0xa68733c3c381062a0aa,0x9b80404348a487c18311,0x108a5803d0260280cc01,0x2161e1615061c3904803,0xa5e401901200a5e42c01,0x5c099fb3897802080260,0x17102828040cbc188834,0x25c24084199c0d806182,0xe1e050e8b050823208f8,0x3b06968f88b828b81871,0x7c25a0622c10b0187068,0x483963a3404222c00610,0x2a0e823c207036286870,0x28068808a3866ccf0e3c,0x44044c32038361960801,0x120303010301e8058200,0x1d010103010101031201,0x20ec0f1113131517191b,0xea0909090b0d003a0f1c],
[0xfea00ea01e0ee1d7a0f,0x1c0e600e239078ef004,0xda000dde00e21c721c72,0xd20cd200d200d20cd20d,0x33195a000bce3300ca0c,0xc23118520ac200c200c2,0xbe09ba0120be0009be0a,0x8b60100b608b20009,0x14360006a607aa153a,0x9627059a00059e271432,0x608e23049212220004,0x160282200e24111a038a,0x17064201853605030010,0xa306230f8215131d090f,0x339a5003895acce6d801,0x146b98085600d67efaa5,0xbfe740015e668f46020,0x11eb981d244409802ba8,0x6bf838d0aba80d9bf020,0xa417b5dae81f8003dae4,0x9069e93a06c02bc815fa,0xc02be807d7fe381680ae,0xc1021aec02641f583024,0x6be8024abc33476bb80f],
[0x40b00afc1e41eb382007,0xeba8015f80046b880171,0xeba0a02bf84d81598002,0x19218204454385af40f,0x4c0505001200120cc2e4,0x588241405004401a80e,0x390e301602e9405c0392,0xb8420c5816051270e644,0x203fa4000fee203fa400,0xbb840fea000fee000fee,0x2071c401c0e6000ee61e,0x1b01dbe6000ee6203b84,0x44001b6e1b6a0dda0dda,0xcd635350cd21a621db7,0xbce0bca00ca0180d600,0xc6310bca0bca000bce00,0xac6000ac60ac231000a,0xbe09ba00ba03155f0c00,0x174a0009be0009be0009,0x8b62022c420590408b2,0xaa2b07aa2022c408b200,0x3c0d68c07aa07aa2b07,0xa206a2201a84201a84,0x59a059a2713526406a2]]

def tile7 : List (List Nat) :=
[[0x819602459e00059e059a,0x96000496000496049200,0x8a00038e2300608e0004,0x8202038e038a00038e03,0x1016200a040282101202,0x1050542050a00028600,0x5050505050505050512,0x5011212050501050112,0x26050505054205050505,0xa088e0508d607050501,0x5084403a82c01010201,0x8a004205040e088e0216,0x74ac2efe002e82030500,0x201405a800a831064d61,0x4b0000bbe42e32c08020,0x2a12c40a54214c01905a,0x180855794c01285201,0xb0231000dc144a22ae6,0x1b80806314c01805201,0x5d4b13c012c4a018052,0x4e021105d52134140211,0x3302900124b12c4ea400,0x3814118308013497744e,0x4e0a783808441bb84498],
[0x2c02810a82221114c200,0x1c814a110c031c814884,0x9c411c061c810a9a6c06,0x7010883434c42804020e,0xb10c04220ecc411c5810,0x4020e9de11c2c1b014b,0x504d87654840805910c,0x91078b4460de1b0f402,0xd0ec2506422b20ec3c2a,0x4c0d000b20e40a0b80dc,0xa1ed1878c83e52051076,0x543a9683a8f170101839,0x360b0c32b47c008b808e,0x5bd0d400478c840bd0dc,0x21ca2c356f4328051609,0xb18328140a3160cc01c0,0xd19c0dc00e011ca2c37,0x9e88e4080550cc00702a,0x4e0cc0a00873210d3,0x28814030ceac0bc3c0f,0x60802c0bc05860c358d,0x30da3e0bc24f8ee0814,0x3819063b40b48e14ee07,0x1c021ca3439eb02a800],
[0x5f4f0ac060d856059f4,0x280022c30e13c3c2081e,0x4228002045861431e782,0x36a78208022c309a33cd,0xf40787c002508c05831a,0x309a37e7823813c421e7,0x394614390fc2382e022c,0x502809a34b202180102,0x86419802809a37f20208,0x78d2332981880e78d232,0x1b0800470a1232064198,0x36c9818801e286021065,0x3e520602c133606404d2,0xd236d001a8278cfc007c,0x8d08070db40074078704,0x8e31c681080e389c2220,0xc11829a24472705c0341,0x1635e441080e864e3349,0x50118e34e097980589,0xdc160043418e31c09b98,0x5a171717171717172a,0x52150052151500521717,0x13131313150052151500,0x11111111131313131313],
[0x42084611084600420846,0x3a0f0f003a003a0f00,0x320836083e00be0f0f,0x320836003200320032,0x82e002a002a0d0d0836,0xaa002a00aa0b082e0b,0xa2082600220826090b,0x1a082608260826002209,0x707009e07001a081e00,0x8160012001a081e081e,0x5001208160012001205,0xaa0520c41aa614056e94,0x56017145017422c56401,0x27a40c17149205080010,0xd3e004214a69c040801,0x1200320c32091698ec00,0x8e0105004e0100960505,0x9d0f010814e5b2010906,0x84d3de4c51039581b406,0x80aa017cd3805c047806,0xcd1b2029d649b08050e,0x1c0da01380000120538,0x805c0d303c043901a04a,0x168480301706180a6c8],
[0xd1a3949c0302b008014c,0x990077004044006051f0,0x5b441264ea2cf5546600,0x1a8b58a34800df00a63d,0xa1e01838380b058970,0xa700015928a428ada016,0x59d400b1005ed2004400,0xd501680107403700a3b5,0xa0c41c480c2300b80e34,0x403700672f4054048881,0xcef00dc0ac55405c01c3,0x6a80712f405416301210,0xa08900a0b2804c050230,0x29a092e017ab8015802,0xca011800a02342e803,0x802c0781d80c8c02200,0x7307805e075000342a2,0x1e0a60002ba01380005,0x544f40440095062a0623,0x82b404502bb5c0162e80,0xe6786870e8061d051016,0x201a00256e800844dd0,0x2a78082804023300c39,0xc028140960174029c48],
[0x90156afc04f0009c5310,0x3a50e54340b018707044,0x660178279070160e5891,0x706e0d85270318dc0e79,0xc0b2053f3c01382a0283,0x5e017806060f41f80a01,0x831680a1458620720533,0x6050354cf00550345a06,0x314ac023c0c090285090,0x75e0162652c1c2424c1c,0x160aea81f49b01627,0x800205206a0c8325033,0x800e0380c18811e0001,0xa0ce018059cd5abc1004,0x780061451e04400a0040,0x40f404417033009e0001,0xc300ae8ac04413388614,0x500c900ae0fc00400,0x67008958c04c2649430e,0x4e03b0152995e1806c0,0x34faf005301f06a0fc05,0x3c260bc008339183c190,0x5abc047008492ca560a1,0x2784c0c80e1438e0e80b],
[0xca01334c0054ca30bc04,0x5003801c04a937012830,0x2014b04f79b800633e00,0xe60255d8328106803c02,0x10b029186c00c1903f01,0xc7848fa050737015802,0xdcdc0490008220d580d8,0xf0e3b019c62a061d034,0x2ca00013800884e3088,0x183841409c0f4120506d,0x9b02700f804e02cea33e,0x22819c65013931014828,0x2502a76001380c6266f0,0xd40470c61140484d0090,0x8130ec12338340640001,0xa89040540045124b2190,0xc900b01a40440e28b300,0x1ac3339428267026fe00,0xa025360e805050181388,0x12184e2075322a50502a,0x45011845c1983828028,0x66052433863a813f4a0,0x515660178099e38e866,0xc54068044c1390184ea],
[0x681709c405c1693e20b,0x40540d252d0128941ba0,0x2ce7596b8060482f803,0xb0b4090fc0540886825d,0x39e3c0a060b03969fc04,0x10c4e36090fc1a06108,0x781c20d01706cd2d0118,0x64102c2cf8b88000502,0xb9008bcb804c0b0ad019,0x67d806880634d6ecec18,0x519400202b032080153,0x301c080002b24854280e,0x81b0be33580f01340a40,0x80459b4054238970162c,0x792a2e385001e4012018,0x740a1c2d006021e0120,0xc57014d11c3a980a3644,0xb038e1f00550009c0343,0x902870b41ca040430500,0xea000128088a45491900,0x242d00302e80ccc1080,0x980facf8ea823a88016,0x178012101c0640260bc,0xc3d06e85090520e4f14],
[0x54060059e4ec0ec03c0e,0x514f832b06291d017801,0x41002f03101c0900a0c,0xd4070a220b038334c74,0x12808a5c02704401600e,0xaf47ecf403e401120e40,0xc2702bc7301580cf005,0x38019212f40b408203,0x68a10803700a2a0abd52,0x4500cb00a9b0004401,0xe02781b4d8ab1c0b5012,0x3416458216000016091a,0xd740440508b700ab5480,0x3e05c0040067983f803b,0xac9140178e5a0882380,0x2c3811581d8070a120a4,0x20c8282450043000a108,0x3484071d81a03c0278a7,0xa1a83080c804e45534b8,0x142290367dac05100150,0xf601020f01200a0308c5,0x564b0c811b86a146708,0x30687e0041f06c285c0c,0x980d0cd1b81e16041804],
[0xd80004c49c735068180,0xb053015a0cf006e04180,0x614b40dc050628ce8129,0x20041804100165180b00,0x30e40503a04c0504888,0x386b2572c21000419858,0x450a80d061680e8711a0,0x3c80380b01f0b0012818,0x42d65011301200488260,0x29482280703c05057c5,0x103ac00ab81000870bcf,0xa180a03419a3503b0141,0xf804400052d36709e02,0xf82b002ae2800a50051,0x11601200cd148e035805,0x9e0903a044088bc20cc,0xc0d01962280cc4010328,0x4f088985332a70d01,0x430241f00681040481b,0x680506207860303293c0,0x211488e703c650780e0,0x8e1a1080a010a760f06c,0x2b39ac04c0042613c81,0x38095c047010101201fc],
[0x9d3a0042a0e833809958,0x408c094121f0de0148b2,0x112602300333d0388c01,0xc0a83a04e04c0c32b020,0x31c8002021b38e314ce,0xf0f007819002150f40e4,0x338cdc0a389958358009,0x54160af2ca896e607a0a,0x5e01580e28af00150000,0x87a02c2281a81a158021,0x540760b5bd00440aa5,0x800f049809207e01e33,0x4807817014284a3e0150,0x20008349111199c81a0,0xd1500078729422ac0060,0xc4c92a2609c026150719,0x80298d9bcc6b806f2089,0x300f40270ec05c096079,0x8231b009bd100161b400,0x345240700c80ce210581,0x36f360045001a594e330,0xd70cc048520a3903900c,0x80b0505c45015802a6,0xc773681136f02a0a8188],
[0x580e508400854021454,0xe1c62221300005b0010c,0x728c2c050585a0e508a1,0x40120005152422e5702c,0x7d01a18105929301180d,0x90585a04606482005cd8,0x2a0339b0d6487004d000,0x708a897f401848241b0,0xa3100a6001040c930128,0x1022d0c600050780f21c,0x21f0a908405c10204016,0x90c8001601382ec01f01,0x811016124801203c1280,0x4212050505050505120e,0x5120505050505050505,0x5121205123212050505,0x5009632051205120505,0x5009605050505050505,0x5050500360505050505,0x5053205120505050512,0x120505123200361200c6,0x54a1205009612050096,0x5050500960505050096,0x5120096321212320512],
[0x5051205050505120532,0x12051205009605050542,0x5050505050096421205,0x12050512120505050505,0x42050505009605050505,0x3c806cbf805c1e0e05de,0xc05d0234c30128328420,0x48807d3f805432638608,0x82d81863f804700481e0,0x4cc4265c0466a485404,0x8818001b00003f8044,0x1070166338a201d819fa,0x8e8320e200050e002800,0xa0fa0000fd01480144a3,0x5faff01080421378982,0x9fbc22f00016110d0224,0x8201180500c095017a00,0xf4041001282a04380dfa,0x16046d814284a2e80003,0x2041014a000128019845,0xe18fd012870a1b30586,0x7e14005405825028a2c8,0x6b0230fc013801cc1900,0xfc54180942741d0741d0],
[0x1583020681d041018a0,0xc00803026620230224fc,0x82e02302050001480292,0x220028c600410c4940e5,0x144801c11780211a012,0x36804dbf004c10cc0300,0x9c0310180fc011807a0,0x79f601d09b0118012c98,0x6c16809d0fc01781638,0x74580e1343409e829205,0x11d08c070e645e0004fc,0x6005818ac4005c0005cc,0x40b80f80012908b40212,0xe8334420088a9e01081a,0x22c39fc020e40510027c,0x609e0600f9015801c104,0x113012062104b80502c5,0x5c5b056025804400801c,0x380c2a05a00f8054a700,0xa0b4140810240610f901,0x408781c80800027cb8e7,0x800050f60120e68a202,0x425436800601bd1601,0x36006090560004804808],
[0xd81c03031cbd804f048,0xc4ee6ea0205830901c02,0x50f051218833b3d80590,0xdb32e23361106c0c2514,0x2587b01a809a00010802,0x2f012800001202310010,0x8050850820020ca04f8,0x541928202c00010001,0x8400800c008417008400,0x1081989d01600200300,0x80206c028cc1e8000f6,0x8105c02806a0000c601,0x7800a02c11807b36cf54,0xa1d81302a0560cec3901,0x50540632710158c46509,0x288a03a0428b82c2d0,0x1802e007808980004c,0x5c39a6190040de005e02,0x100e1a0c600280871b80,0x232808120e837946805,0xca1318e5c1861a008295,0x629481d0200464047000,0x5809e709a22060b80cf0,0x20a270041f04d2f201],
[0x80a1cc24911016022a7d,0x61ced012802106e8039,0xc3b404502f040d013096,0xe1c65018e22148c03833,0x8631a20024016009988,0x604c0a1cb201281161fa,0x6418c05416804811c6,0x2217c0013c96441c7003,0x3f04c8076ae004c1151,0xce4c28232c04e6cb0138,0x80d018d40c4878015810,0xfced01580228783e08,0xc58e83c0b05a070c281f,0x60c114d82303b4047002,0x441442b0c805046073,0x8706c04c002f0089ac,0xf81d404031201181831,0x20c1a202090001084a2e,0x95405c000511f32a0021,0x104012058443581cc050,0x38380d80820496a10128,0x800030e402a92c04413,0xc82f04c0bc0436a301,0x184e0420188087008374]]

def tile8 : List (List Nat) :=
[[0xbe04c19028860634e701,0x1602250514773900a2b0,0x3003c502108162432063,0x31c6082160a827380004,0x5c10e1c260433d0245a0,0x50a3e01f009c009c540,0x40f062808700005400,0xe06207e0706001000148,0x23721ee185605410f04,0xd011404699804c049012,0x5807c033000202220800,0xc0188046a1cccc0284,0x273c8d700d0260edcec,0x2100c072011a0d034000,0x3a06200a802ca3c05c06,0x1008538809c2131ac801,0x1438c0e0043001e12b80,0x42e03a02851404048050,0xb018060634e101680421,0x70079012124c5f01a0a2,0xf0451cd5061437090405,0x4405b22e498c0a28a020,0x45c0d01780090003840,0xd8010801564b940be013],
[0xc0441a4062f0020f8230,0x1e3068f8041060808745,0x8413490881d80240d19a,0x1120121160126800c30d,0x1503e003801091c44054,0x1780bc050c6521013802,0xcfc19c2751aa83c7170,0x8700001580602c05e09,0x883062380e80a1780c64,0x1027c18802a00703220,0x607c500021003ac44044,0x50380307434c28ca003,0xa002000138061288403c,0xf00183e00e028a6c1b81,0x20460822c082314b6004,0x84a1110542f0040e0180,0x90160b0909b000013801,0xc2c46ed8015802770140,0xd016028a405803600822,0xb039e1440234017821c7,0x9c0a015830b627a04603,0x7861282e0340901c6d85,0x3613809426898e246f01,0x840080414ce012822f0],
[0x601108b44004c0511,0xc072040206012810e012,0x4c21006016004a070291,0x8000503305980068000,0xb6028882e008044026c,0x3f4002059801b8084cc,0x8c809b1c02081f00841a,0x1a02804c018503d011c0,0x47023a20016057012c0,0x305008095090630cb38,0x561d67683737058160d8,0x108084251014507c0dc,0x675812289202380800ce,0x282280540906818ca802,0x120025005c8080044c,0x70241c335cafc043000,0xbf01280de11c80240b87,0x6802e80b81e0e584861c,0x5c0a68a4010c8000601,0x63440c025fc8033028cb,0xc00011804521c403a0c,0xa58a013102981c80c140,0x440a602d800007004c10,0x16203016003300872c40],
[0x5052350e01621d16016,0x961205051205009605,0x5050505050505009605,0x5050505321205120505,0x5050036120505050036,0x5051205050505120505,0x96050505009600961205,0x5120512050512050500,0x96120542050505121205,0x12050505050505009600,0x4a003605120105120505,0x960505050112050505,0x960096009605009605,0x5051200963212050542,0x96009605050505050512,0x500964a009605121200,0x45264c00c19205054a12,0x45340148c19601082602,0xc241960ec1180e1086,0x4400221030481085265c,0xc1bc09149800b0030906,0x80980310864c04cc0308,0xc2190807102250052c0d,0x4250053c0a4108285094],
[0x61c21499280018120140,0x702f10052c0290317050,0x652c05c0f04246453400,0x240480642452c442028,0xd094022ac51403a1894e,0xc504035802e8e62404c0,0x4225040418b98e0a0e0a,0xc5140a0e85062401d808,0x143a18880741180a000a,0x400e051401b078841428,0x8b81a1889894680b8010,0x30ae3814083c1061a9e1,0x2830a39894180120b828,0xc0308b9894180782a0b8,0x802198b81458044160c8,0x2e862c01e161a9e191,0x8c03098b81408010822,0xb18203413a00b1823a09,0x7844ed861c020bf93e00,0x48031006082fe4ec420a,0x8825320c5c14f1b29398,0x13982030460f1983413,0x6808c2c60c01813a0061,0xb8b06460f1b41813d872],
[0x1b0f80d022cd861c1c39,0x1c6e2e004010a0b41398,0x83413e0420586d8ca6,0x3b80724c3e4004d003f,0xc183e087b9932802297a,0x60b0d4092103fcf1f070,0x883d00102103e4d401e3,0x180380c050780c22b98f,0x43fc11f0460e08bf0f93,0x3800793202801802272f,0x4540b4715078840f93,0x3d929760360672f43f4,0x310460f05cf64b4005d,0xc800c0c80f0102a885dc,0x3c30601008729bbbd92,0x23d97601618820ed43d4,0x181f03c29873b929802,0x2ee4b400439a23cf65dc,0x3d92b80221722a0f0100,0x4ee3dc18540c541cb197,0xee03e9206e00883a144d,0x840049003b003b03ca90,0xa803a1a484013800c3a4,0x2e048460d00c3a49c03],
[0xb81e4047c1a48c0030ea,0x84041824391819bc920e,0xe1782020c3bcfc01a024,0x2280183846400470782,0x8e11a800611a00470047,0xa5a46400618304607182,0xc823032183847c022807,0x18042c029e9188005b01,0x708c04400e439c017018,0x241c540e1028e118801,0x2801644364284a2e438c,0x26188183616454003703,0x6084440120b4008e236c,0x1601a8008e2364016803,0x8700c182388dc800a161,0x81908801589a03604c43,0x400d234c0020300828b6,0x18d6011c070064234c02,0x123e1b82da1443c0348,0x616021c9c190818d28,0x84906010048ce0013,0x41241402a00c0c00432c,0x4c190010c981a04c047,0x607404741241c061c01],
[0x17170130a40020432c01,0x5a005a171717005a005a,0x151515170582005a1700,0x56151515005208561515,0x4a13004a00d2005208,0x4a00ca1300ce13004a,0x4200421100c211111113,0x3a0f003a0f003a0f00,0x2003203020d0382003a,0x2e0b00aa0b0282030203,0x2609090909002a028208,0x10182009a07081e0708,0x12010200120816001205,0x3de9ae17b5f7ad3af15c,0xff0fb0f19dd6b2dfb4ee,0xae0cd1bc2fb5c862546,0xcf3beeae51d45b4ef9df,0xa3e96d6bd410fe9fb1f6,0xbaf53e79d9dcb9be7b01,0x3e46df3d7bc99b9ba13f,0x5ea379fe3fbbf5cef3e8,0xf0c24b86ab79e993588f,0x59ecfd5f86ef3e3cda9c,0xe98e29dacd4dcdcc10b1],
[0xfeff4fd4faef5df2eee7,0x699a8f78778027565282,0xdfbd48c9fbf2b4dabca2,0x25c3ab49a45fbdf68eb0,0x2e69e36e11defdc4d99d,0xfe2fc0fa2f5bf10ed5ea,0xfc96e8cb84b7805252fa,0xcaac40bd6b58ac3a5c9,0xfdaf77f11e99e1edaed3,0xd4d70d29ccebe6ade96c,0x1ec7e9ce79e58e24df9d,0xffafdafa6f7ff69f2af0,0x408c482a7be72952b2dd,0x2be8b62ae1a8da0998f9,0xe96e3fde3d53d06cb7c4,0x70cd2c03ac9fe9f96f02,0x5ea5e8ae6de4ce21dd9d,0xf52f3bf22f10efbed2eb,0xa8ff2fe4fc3facf9cf7d,0x8b71b319ff96483d6643,0xd73d2ece4cc7c9cc41bc,0xfeea7e78e44e0fde4dbc,0x88d5ff2fdcfb4f7df56e,0xe14ddad68cc4c0fb38a3],
[0x44f15ef8eebedcec1e90,0x8fa2f98f8cf89f77f70f,0x48e2a9ff7ff0fdffc4fb,0x598f589e84e7a2735691,0xeb80b2eadfa60a1c9d09,0xd7ed3ace2c93c40be9ba,0xe1f9ef2eebee62dffda8,0x6d29cdcc6dbadaf7919f,0xe24deedd9db8d90d81d6,0x3af23f0eeededaeace48,0xffc4fb1fa0f85f7df66f,0x7af73b526351ffeff8fd,0x2f9fb9b395d90d8b7845,0x1b8db75b31b09adda77a,0xd4bd20ce6c6fbf1bceba,0xe1f3aec7e6de07dd4da2,0x2d72d05c73bb9a4fff4f,0xe3ae13dfcdd2da8d8ed8,0xdaebceace99e6fe61e4a,0x5f45f1ef12f06ef3ee3e,0xffbfedfcffacf8cf75f6,0x397f06ff6635d03c422e,0xaa109ac95691d8a68608,0xbc6b7db4eb19af9a8aa6],
[0x8ad4fd05ca1c7bc5bc35,0x6f97f4aed3e7de31dd7d,0xcbec7dc0eb4c960ffdfc,0xb2d9fd86d43d37d24cef,0xfe6ae68e58e1cdf2dd2d,0xeebed6ebfebdeade7fe6,0xd0fbefa2f92f64f3af09,0xc5423391ffffeff5fd9f,0x88c83c7e277f70b6625b,0x3fa23a029bf9589368c2,0x4b3fb20b06aeaab1a7fa,0xde3d3bc5abe8ba2b86b6,0x8df63f2ceebeb5e74e4b,0x7cc2c7ababae59c0fa5f,0xe1ddfcdd1d92d67d2fcf,0x9ae90e65e55e45e38e2e,0xeee1edeec4ec1eb4ea4e,0xf7ff78f6bf3df0feffee,0xe8ff9feffe5fd8fbefa7,0x28717fb75f68f6324352,0xab2a56a109df97291f8d,0x4ec32c14bd2b5cb3caf6,0xfd17cf3cd8cbccabc84c,0xe7ee5bdfbdb1d85d4dd2],
[0x6effbfcafbff5beffed3,0xd28cf6c97c3cbbbaea9,0xdffdecdd7dc2d9bd74d5,0xdcecfeb7e87e4ae32e0e,0x8f43f3bf2bf23f20f0ee,0xfa3f93f7cf6df60f53f4,0xbfffefeefebfd4fbdfb3,0x63960b5dd5984d03211,0x91c90d8c87e17a372065,0x20af9ab4a58a1399095a,0x9bd2babb94b75b56b47b,0xda1d82d3dcc9c2fc10bf,0x67ef4eddebee88ddfdc0,0x3b8cb21ab6f9cf8df7ef,0xcccc1ac1ac1ac1ac1abd,0x5bd5bd37cf0cf0cf0cf0,0xdde9dc5dc5dc5dc5da2d,0xe78e78e78e78e31e0de0,0x6ebfebfebfebfe9be9b,0xdfb9f95f4ef2af2af2af,0x8fe8437b569b4c2256fd,0xafa6ba45a149f69b4937,0xb7db72b59b36b0baeaa,0xc63c59c40c32c0cbc0ba],
[0x66d3ad19cedce2ccac9f,0xe5ce40dffde1dd1d8ad,0xfbffa3f82f47f2fedbed,0xa9c65bceb00a608a2fcf,0x6dd8dc0d90d67d40cc6c,0xe4ce40e2fe20e14e08de,0xe7edeecfec3ea1e69e60,0x6f4ef3bf28f23f1cf13e,0xf93f91f8af85f80f6af5,0xeffd7fcbfbcfb4fa5f9d,0x25fc5874fc370209ff6f,0x86082080d7b776f70d6c,0xc49b39a095d9078e08c7,0x4aa3a7fa50a379fc9dd9,0xcc2c5ebb4b26b10af4ab,0x62e54de7dc6d80d61d13,0x2f99f6cf3ff2be8ce73e,0xaada3b9c9ff5fd6fc0fb,0xa6d5ad3ccffcbabb0b18,0x6e17e08deaddbdccdbdd,0xe7ae72e63e5be3de35e2,0xd6eceecee99e91e91e89,0xdefeefeef6eeeee6edee,0xf51f42f24f1cf1cf1cf0],
[0xe5fe9fe9fe1fd2fb4f6f,0x47ae7576a25cc51b33f1,0x8f28c58ae89b8518227e,0x38a2ea099f299d95f938,0x4b11af2adba89a6aa49a,0xc28c0dbe0b92b52b3fb2,0x7ad49d28ce0ca2c83c4b,0xdf60eeaed3ebae9fe08d,0x8b1ffcff6fecfb8f9df8,0x55c06bccb53a9c9d4936,0x9d1cd0fcf2cd1cb4c93c,0xde8dcbda6d95d84d63d3,0x22e1ee16e0ee0ee01df4,0x7e7ee69e5ce32e26e26e,0xf20f20f14effea3e9be9,0xd6fb5fa4fa0f98f73f4e,0x35043f5245ff8febfdef,0x6a168c66a6526225d256,0x2b8917cd7367116e46d1,0xcc0cbb2b03a71a1498a9,0xcd0ca6c99c77c6fc67c4,0x69d5ed46d2bd16cf6ceb,0x4e49decdb4da9d91d79d,0xfbcfb7fb2f78f1ee9ce6],
[0xe2ffdff8ff0febfe6fc4,0xbbbfbadb9eb69afb9d27,0xc28c10bf8befbe9bd7bc,0xd5dafd65d06cd7cb6c6c,0xed4eceeceea5e52e37d,0xf22f07f01f01ef5ee0ee,0x76f64f55f4ff43f3af2e,0xdfbefaff9af8ef8bf79f,0xff1feefe8fd9fd6fd0fc,0x4556a3ad3ad000ff7ff1,0xd6b669968467766664d6,0x89a80b7b775a74971b6e,0x3191c9189108fb8e68d9,0xc96895b95794a94a9429,0x9a199997c97496c96c96,0xc8bafaeeaa6a309a99a1,0xac45c3dc3dc39c1cbccb,0xf8aeafda6d3dcaec91c5,0x8ef8ef8ef8ef8af8af8a,0xfaffa7fa3f9ff9ff8ef,0x9b194d7d17d1feffcdfc,0xbaaa1a9ea98a85a75a2a,0x2b47b18b08affaf2ad9a,0xbdabd7bd4bd4bc7b9eb8],
[0xec08c05bf5bf2be9be0,0xcc2cc26c26c1dc14c11c,0xcd1c90c6bc52c3cc2fc2,0x61d58d55d52d39d26d19,0x8ef2e60e0fdb2d93d67d,0xfa3f9af94f8ef81f7bf7,0xbbfb8fb2fb2faffacfac,0xd61d56327fff0fd7fc4f,0x68a65d64164163563161,0x136d66ba6ae6a669268a,0xa83a7577437337277237,0xa9ea4599b8b888f86285,0xa4c5bc1ab68b48b3cac7,0x8e34e34e20e1cd0dcf5c,0xe89e5ce4ce48e40e3ce3,0x84f3ff0eee1ed1ebde99,0xcfa8fa4f98f90f88f88f,0xfdcfd8fccfc8fb4fb0fa,0x17ffcff4fecfecfe8fe0,0xebcebcebcebceb67a728,0xc09c06bf8bf5be7bd2bc,0x3bc3bc37c33c2cc10c09,0xec7cc6ac66c66c4dc3bc,0xda2d7fd58d11d03ceeca]]

def tile9 : List (List Nat) :=
[[0x2fee1e97e82e30e17de9,0x6f33f33f33f33f33f2ff,0xf92f8ff7df68f56f3af3,0xcbfcbfcbfc8fc8faff9d,0x1fddfd2fd2fcffcbfcbf,0xff5feefebfe8fe5fe5fe,0x3183178240fffcffcffc,0x987186c84f84a84583b8,0x8f88c88c38b589388e88,0xc9ba9b599398097b968,0x2b08a6da46a41a2ea0ca,0xe4ae40e0bd27ccbb81b4,0xc7e97e97e92e84e84e62,0xcefdef3eeeee9ed6ecce,0xf25f20f20f1bf16f11f0,0x5bf5bf56f51f42f2af25,0x7fe7fe2fcff9af73f6ef,0xff1ff1ff1ff1ff1fecfe,0x34c34c02b0879cffbff6,0x6c66c59c51c49c45c34c,0xc8fc7ac76c72c72c6ec6,0xd2cb5ca8ca8ca8ca8ca0,0x8d5fd3ed0ccebce7cd2c,0xed8e99e84e3dde1db7d7],
[0x1ff1bf0ef0af0af06f06,0xcf2cf2cf2cf2cf1ff1ff,0xf51f4df4df49f49f41f2,0x88f7bf7bf66f59f55f51,0xcfecfe8fe8fe0faef99f,0x435000ffcff4ff4ff0fe,0x917407146e86db67e67e,0x68b68918847e27dc7c37,0x9ff9f39f39bb96494592,0x18a0ba0ba059ff9ff9ff,0x9a43a3da31a2ba2ba2ba,0xa81a55a55a55a55a4fa4,0x63b63b56b49b43b36a94,0x5cb9cb9c7bb7cb6fb69b,0xd47d41d34d2ecf0ceacc,0xa9fa9fa3f9df20f1ae02,0x9fa9fa9fa9fa9fa9fa9f,0xfe1fd5fc2fa9fa9fa9fa,0xb1a9aa5fa489976df6df,0xeb63b43b31b16adfabfa,0xc2bc1dc06bddbb0b8cb7,0x66c61c4fc4bc4bc3dc3d,0xcc8cc87c82c79c6bc6bc,0xca7ca2c9ec9ec99c90c8],
[0xf9cf4cf0cd5cb5cb0cac,0x8d3dd02d02d02d02cf9c,0xddddc6d8fd8ad81d81d7,0x6df69eeaed3e06dddddd,0xaf86f82f7ef7af76f6df,0xfa1f98f8af8af8af8af8,0x6ec58f2dcbbfe5fcafaf,0xcd01c98c1efe3f79e7cd,0xcedc4fb8afccf75eb5e4,0xd9fd9f63e28e28e01d3c,0x1ed1ed1ed1ed1ed1ed1f,0xe66e66e66e66e66e66ed,0xdb7db7db7db7db7db7,0xc0a20a20a20170060050,0x5e05bf49b18d18d0f80d,0x6475f75f73c72170d6dd,0x988e84e84e7d27727707,0xa8ba8ba1aa0d99495394,0xa2ba2ba2b1bb1bb19a8b,0xcc9cc9bc7dc7cbafbafb,0xda1d73d73d73d73d73c9,0xf7df7df5df4df3debdd0,0xfe2fe2fe2ee2de28df7d,0xe37e37e37e34e33e31e2],
[0x38e37e37e37e37e37e37,0x8e53e50e49e49e49e39e,0xe6ae6ae6ae6ae6ae6ae5,0x6ce6ce6ce6ae6ae6ae6a,0xae7ee7ce7ce7ce7ce7ce,0xe8be8be8be8be8be8ae8,0xc7eb5e9be8de8be8be8b,0x7eddedbec7ec7ec7ec7e,0xfffffeffcffafecf82f2,0x7a07907607407406f062,0x308d0890890890820820,0x50b45f3b426009409409,0x98c39a3e8887e871f608,0xe030000f35eb1e6fe3dd,0x1431150ee0d20c007e04,0x712332131e01b318b171,0xc83d7206685aa4222ef2,0xdf2d58cd1c14b119f897,0xaf6c55ea413000fbeed2,0x685c85180c7f57e17d57,0xa0999a9129008f08b287,0x31cedc71c29b64ac0a61,0xff2fdaf4fedde5fdc6d,0xa2d9c799c91187c5b200],
[0xa3b82b53b28abba82a47,0xbdccd66ce6c69c12c09b,0xf85f5df0dee5eb8e8be3,4037,0,0x2801800400000000000,0xd9ca4e767582411199,0,0,0xdb14e03802401c000000,0xc8a91058a4292,0x30f00000000000000000,0xf30f30f30f30f30f30f,0x8b98b98b98b8cb847b73,0xfad000f25d21b98b9,0x15000000000000000000,0x50150150150150150150,0x3931b405503502001501,0x410d6000decba37a6532,0x17b065a49940e2b82021,0x3b1eb4cd3b3da7d94787,0x3b8ba88f8397aa69a5c3,0xcb14abea93a4b9e79839,0xd26cd0ca5c4fc16bb2b5],
[0xe1eb6e7de19e0bdeed5f,0x7b6e7b0000fb8f70f28e,0xb209e014fcbf96f61e5,0x290da0da0da0da0c60c6,0x41291291291291291291,0x7286c66015153ee32916,0x4fcd9c3cb63a7796388a,0x21bd0e9094015000f14e,0x2bc2bc2bc2bc2bc2bc25,0xe350f4652fc2fc2fc2fc,0x6b9cb07a9d91f7b66625,0xf96f17deedc4d1ac4,0x5e2c12c123e16d082034,0xeae9a9b9e48ab7726393,0xda9d26cf2ca4c70c3cbe,0xccfccf7ef7ef16efcec8,0xbacf6eb307000fccfccf,0x20dd6cf8c1bc1,0x12050000080500000402,0x2c0800001c080000,0x680e0000520b00003c0b,0xa0110000840e0000,0xc140000e4140000c211,0x16217000134170001],
[0xf81d0001c41a0001901a,0x26c200002321d0001,0x32230002ec230002ac20,0x3c426000378260003,0xb02c0004602800041028,0x5602f0005082c0004,0x7e3100061c310005be2f,0x74a330006e0350006,0x904a000820380007b038,0x9b84c0009244a0008,0x884c000aea4f000a504d,0xcc453000c2052000b,0x7807000d6e05000d6a02,0xd9a07000d860a000d,0xc000000db406000da806,0xdc000000d,0xc006000dc080000dc000,0xf0a1f000ecc1f000e,0xbe19000f861c000f481f,0x10221a000ff019000f,0x8c0f00105a1900105602,16,0xf61f0010e8070010aa1f,0x11721e0011341f0010],
[0x7a7127cd1ce50011ae08,0x3c68637029574f2bd1ba,0x434ff8db0646ad10803e,0x93697592c15e797873a2,0xb07d29db994a11ae6f90,0x2a4713977cd67de94f00,0xbc53703b2b6ac6f7092c,0xe26a562ca3a892e87ed1,0x334191d41e058596850a,0x6cba86081a40fbcba54b,0xeacb0592a8334dc31a6d,0xb57668f2fadd2b05c149,0xd6a78e30ee9716ede8eb,0xbe39e462460b7769d199,0xf14105ee55d9e8fc1e52,0xb6197a4fb0ce9bdd24a8,0x11503923674874d3705,0x1c7d66ae1cb0ab7187d7,0xce9d31ab5bcf6fdef1,0xc8a38eabbe7f81dc7e2,0x775f3e489b55d3a8a814,0x3f17e2dcacc5bf416d57,0x5f8da73b82adde0853a,0x8f44b3315c52ef000d0e],
[0xbddea5dd6bd3a581b611,0x5af85b4c8db6b90f96f3,0x5dfb08b5068775a8f23f,0xd3691bd2eef1429b3adb,0x6269e921269d9b735c11,0x7bd8a3109a4e1444d0c8,0xe5217afa5cc0211d6898,0xe93fb8be2e18740d350d,0x1cf82cf1fc83ca8a7df,0xda2cb6b6c3a089a074ae,0xcdff56aeeffbff1173d5,0x449ad0e61fe8abbc0fe8,0x48b23a3d251250be70c9,0xb7d874dd7b2570bd733,0x42840ae8488eff19734f,0xa2f6fd4ac10e7ebcefad,0x25d0ae9d4aff0024be5,0x598642ab485e495e4c4,0x6acb97cc2d24baafdae1,0xbf8bb8e25759facb0972,0xe80360a1fadbd1d18713,0xb170f2427c8f9c81e041,0x84b1a42f48706d5d5e1b,0xc92f4f6a052fbbb0b14],
[0x6913a2b68aa4d4ece3be,0xf1e5a6026e3c01ce465d,0x352f9eb90cc7867dfe0d,0xf1d91d2c743061b61f6e,0x740147999c487017b8a7,0x26d6d13f48f9b38fb256,0xe2ad412a7cfc09a8a3b0,0x92527bfa39792a1948a4,0xc68d77d256b0a558c2de,0x44ee98290340cf5e968b,0x5d166f1b1e4b9d1eaca7,0xa1f6fabb97b1ff35c6fe,0xf26f0031142135781bb7,0x82f470536b8b0f90d425,0x94d6087293c2a0105192,0xb148f011362e925315e8,0xd82606a1be439604c39f,0xe49d193641b955fc5334,0x42254c2dc7a2e2889fb7,0x63a9624e458f67f745f5,0x2331b60109872ee933fa,0x29f7936e61dc28857a68,0x79c16a5276566a78156,0xda9194b485fb48b02bd2],
[0xd5bca6b56b421cdb261b,0x892c6d942df797ca371c,0x9d842a9d439796ae0d23,0x48867bb1783f54aadb18,0x6b963a2ac00aafd3fd3c,0x230584fac6b058a6caf0,0xb20bcc220c26bf7d572e,0xd0c4e6a05a2cc7f0516f,0xff2d6490a1e7c845c095,0x40f6f9bc8764c2fb1923,0x34072b2d9ae44eb74fb1,0xdaf55ac41aea5aef75fe,0x5e9e78bbfaf1beb8cc89,0xf0da98eef2f89ba166ed,0xf51a24dee865deee1e8c,0x4ef1a0e197afefc0696,0x85607ca5b32b65842d1b,0x4e1497120ad60c129621,0x790f702096d315fee637,0x73e7e6b69ab51d9a00d3,0x39434c4bf90bf2338cdf,0xd18db61ea76fe5db1885,0xcbef90aa460a07dfd32c,0xa54efbe634db3f173681],
[0x981dababfbdfc8e5a70d,0xa8ed56b3bb20de732409,0xe1f7c685425b13f63bb3,0xe1855a99a1f8e360bfac,0x382b4c7d038e3359a292,0x2eed32e4902114f12d3,0x12ca1a235efc8a6f396a,0xa2a72d9b55708707299b,0xb0136c63c800de25e1bb,0x7e4c6232474b75912986,0xbd8b886676393d6b9e0c,0x67da0cb0c4b088a7a452,0x2146571a9d263be99085,0xb0c12575a12a7a8ca316,0xbe1715cfa913c5d732ec,0xd9da616ce5c1e22b7478,0xb223c9e14f17af1b2ff0,0x540ff26ac6f1f7b186fa,0x894d4fab7d8e0cad62cc,0x9c965b735ad727351305,0x70d41593c526e56edefa,0x56af559eea5d5369ff89,0x1e5527b79d5860feca6,0x15de54f9a27e16df9e30],
[0x5d844e003aaa21d4e1fe,0x68eeda08bf107f129c44,0xafe38b1daf474dae1c54,0xd45c0718ecf7f0f9805f,0xfa832eb479b56e4d1b44,0xf7bd5731a82cfef8db3e,0xf52d97a605447cd1e9cd,0xcf3dd23226d95169ae14,0x8614b4ebc27db47ad421,0xe140ffb458f4d6701713,0x757e04c90a4d19e754df,0xb6f3af73e217c303acf0,0x7d4cec16a7e246d1a542,0x8dbc88238ddef0f861b5,0x54b7da643e91426c3db5,0x94fa71088c35fe144856,0xd1069c5f9379c32003c3,0x9ee03e31e61220aa703e,0xf438851929b152f70914,0x28d0fb3383fca8e622e8,0xd41c46e6022e466249e1,0x5ab8052c1549abcfa6fb,0xe0276f8c9f2fe80d10ee,0xd803205ddd6a8977feb0],
[0x2537f0c0e5f353b86f7,0xda9d75cdfbd1745e773b,0x8037aef4c885cf2dec51,0x1696d10e1dc65f42a95b,0xe3fe081d905f31c22b85,0xe62931a90b2615914ca3,0xa6458afaa33d2ca862fa,0x4909ed8278e8ac39d1ba,0xffe7fa88292e8cc94250,0xc958a25a8e8884b5d95e,0x55a209eac89b5b050a89,0x5cce16e29e9236c16ce5,0x52c9d2c8da4f9f3b4efa,0x535c6984030ab49a274d,0x5279b854b1005f2f5cb4,0x31c884308c6d79271cab,0x2b0d51967769afbc01dc,0x4bca06744f96f97c3e4,0x146b19c0a84b9a281377,0x6e4cf47ed7e3a82b496,0xb9f01fae210ec413dff4,0x1df9ed0b87ebe98a805e,0x2e6dbc0a483a3859e0c3,0x803b44c4354e61ea96e4],
[0x40f6d6949f2a04e0ab6,0xfb86380af6feba1def0d,0x66815fcfb04662350433,0x2d05d430ec473fe6dc0d,0x3159929296e1aa674ead,0xd1ee3490a63603b2c8d1,0xf7574aaca6ed3bb180de,0xc29132266c4ec84840d0,0xb963e10da67cab56b2b9,0xc0732be31c70524859e8,0x697b60039232ce0f3081,0x2c830c250f0059370681,0x5c7a15d39594a473c5e4,0x1415ddf5a35aaf8616e3,0x75577d30f16961a5c3e3,0xdfd3f1290ab46ecb6701,0x24fdeca37bdecd0fa05a,0x24b8a7a4b004f5240092,0xf19c4f79d630a3283853,0xdb336c73c6d0011e7d8b,0xb49056ac4d805e54ce66,0x7d9dba61b3a8ec632034,0xaba0935f8f8e7dc4ef52,0x26b2a749976e84e4fed9],
[0x4edc6f1c089c041d6159,0xd7f118cbed46a38dc004,0x930cd49211e1a16b4d1b,0xec5e6f8884ebe50b0783,0xa27d4b2375632008267c,0x4c1c06714a1db8344a44,0xe1d2cd692b5349ff04cb,0xa1690b405659e54f1f23,0xeab003d90f071fbb5298,0x50e5f234210439c39bb0,0x886490b54ee93b6dc0e,0x1bda22006999d42e2b,0x63194a5c41d2a1e6b64,0x14c8f59bf479d554ff07,0xd9b6a44ead8429d0b387,0xd489f7ef4371d6cae68f,0x964fde3b037ca2112252,0xf58c2e9a7d87a1aede5e,0x7d159dff159e6f96f282,0x9413a521caba3534da22,0x96af4ff04d5c8257e46f,0xa37507f5094bc4dcc628,0x34a8ded43bf85f256848,0x4c00fee5cd6a3cd6122c]]

def tile10 : List (List Nat) :=
[[0xd4ca4089f3a5723c22dc,0x3faa83a9a1143327fbb5,0x4d35fdf48c767f717e4,0xba0d9b55277736f464d6,0x7978800082a7b3325f84,0x2a466683b69d551fc763,0xa32f66cb55c6630b53ba,0xe206396f0645e8d4f76,0x9ccb92697cd4479bd6a7,0xaf1fe0fe2725d5344027,0x3ab0d18ad7a6a9d72ae5,0x37f1d040938b9125c99a,0x3fc53aa77c78cbfb7059,0xb0574bfbb70f3a6f8fea,0x6b4dfecac08a0a75f3aa,0x8abf0a3a78f279545922,0x937aac301722df627482,0xfceff6ba6f10e656248a,0x5eb7e95e5e104d2770e8,0x53c0fdce58dfa6f57818,0xb54c50c11123aeb162ba,0x4501ba8ef4d408d08254,0x3953e1ff83d55da56953,0xf88b021817094d7de3e7],
[0xe26a4cef3c696ea411c3,0x84b50e51aa1332154f03,0xfb6942fa17017e785468,0x8310676f01fbbda1b437,0xb7734ea65269b30dd4b9,0x2fc85b661b3aef478a2e,0x8ba7a3699ecce166b83e,0x8fa2e3089a6771b053eb,0x2a810c542f589e02aef8,0x4131fd3a8d515a1c824d,0x645256ebc7c7eaea553c,0x73155df1f15d4e1aae27,0x449bc85777737b2f49a5,0xe2dfa3a66a611ce549b0,0x1016b116fe0bd45c76ac,0xdc69d68fbf2dfad06091,0x1c1de439408c9da11fdf,0x964bc5d79c8855ebd59,0x9153a2b4b68e7c5cfe8f,0x461dd3035fe9948300fb,0x7ca59cc4bad7325cb687,0x75ca4e0b2c017cd8d597,0xd13b3a4afd13918e1577,0x82a4485b988e4bf50f93],
[0xdc9817502ab4ff60051a,0x4f195e58bb106781bfa,0x1bb53ba7f1cf12c2218d,0xd697a7ba2a364c7f5c76,0x7e2e99b314c0c702e7f6,0xf1a4c190a0976b94d4b4,0x99a9ffe72309de66428f,0x3d1c70a9d0bf75af9264,0x862ffeb53ff71a05a869,0xa1bcc7dde047f376e0b5,0xd95a09244069064d766,0x254f877d9baf14ae4c90,0xf5a294656b97a90c7799,0xc60540f1461ebecc6f24,0x9de22d63aa6e55b1f432,0xb9a1d54dbfff8ed35d06,0x31f5bdc206859056b624,0x9efcce7cf154d8d0ab90,0x1df61a6e38cb5be31b17,0xff5de2d16b936bf8f666,0x9f4e503533dbcc0c0103,0x5e63afa34a7c1dd4a954,0x2782cb9f861752685db3,0x480c230d19007d6fa7b],
[0x22b919ad9f8cf45f06c3,0xf6931dfde4a42e5eb228,0x34f916638795bc448dfe,0x888e9d01ef4947e6d258,0xbdcf3dd12ce531beba7a,0x79d839cd88af7c26bf1d,0xc9b93b99e09c5b901255,0x76de43aca31647955731,0x94f955cbb19a1dfbfe4d,0xc8d18418852670b74814,0x11503502acdcc7b96504,0x85ff0cbcfc5b4fea1d73,0xb95678c5b51bc8341c27,0x2ef8dc912f3581edef07,0xf36cc14fc20a030be,0x9d1a34dd8b023bb10383,0x9c1729f3dc1e84b7a2cb,0x44620b416b1de5867b0e,0x8470bfe062be9d3c1030,0xa635eed63f689a1adde3,0x2e6cc8c22d9514fe6d7f,0xac5d1d86de50e72397b1,0xd6d624aa8cf0e59a11ff,0x5bb4cc44d88d1f77ae1d],
[0xc8a1559cad03055c3aa7,0x2d336538c02a21a49e89,0x3d12c1c131a7809da382,0x440d9557776165064221,0xa31eb6ebd1a8ccd1cb16,0x3d8f9a6b0299629cd6db,0x9e643169c5c69e1126bd,0xa99082ae0c10956364e1,0x715929500b792e0bc332,0xc46bafc937721eb0023d,0x6dd73620a5a63cd5e939,0x16da69ebaa0e25760829,0x42dc46c12845bbf0c07d,0x27f7275c53acc42caa6,0x98b0644eafa02c8c88c0,0x2c9074e30847638fdfd9,0xb9217c3ba6c415bfd43,0x367b6246ea7934e35815,0xe5079e8a18ec2b8f349,0x66d6df64b0d2247dc5ec,0x63b4d85e2adbabaaae40,0x84853348ac35b768f47e,0xfec9b5b00547b4c003e8,0x7de3ddb9772f69b5ccd],
[0x7bd511f9b8d2cf10b99f,0x83faed406331abfcf0c9,0x5d515063e1a5ecc63eb5,0x74c5e4047ea451e1144e,0xd7e8ae1f6bdd48dfacc6,0x2f88ff5a6486743bdcbc,0xb6eea6b49402ada97805,0x4d0f9d3931abe6f5dbf,0x7ad186fc31888c0a9402,0x945286ada8749f8ae0ff,0xbaeb479337248d898fbc,0xab5249a524a65c553809,0xda89fb17120d821fe674,0xfd63cf02c863205f3f47,0x9e34c02b2b56d69a022d,0x64f9306a1f5c719a65f9,0x9f7dd1ebb94d9c602eb8,0x939706756ea0f04c9ba8,0x3318d737c8bebe866f9f,0x419230b73fb2d283c5ea,0x9a81e6fa339b8de9e458,0xcaf456193234d6c1e604,0xaaabaf4ff59e6cdbc710,0x977f170fd0c25d950a5d],
[0xe36443a983c994cb1b55,0xf7a0b71d782b78960965,0x6bef4ed7ebebe42c6d83,0xee87e45f134d658ab8db,0x721acdd424848b6138c7,0x381c47248eebdf27e845,0x95521004ccbc7380329,0x6682bbbdb52174f4360a,0xc2496830cea80c8f18c3,0xa5edd410c719ada2dc37,0x9dc831c2617200576b0b,0x24fb0a7746aeb06e1dd8,0x3b5a32155446c76d5b47,0xca93d633acce425fd2b5,0x85df3749df24dda3f5e5,0x1c327a8fa1b10c3d2999,0x13c014df54e9547092bd,0x8af1a0baefd57a8304cc,0xa6b42e64818252a779bc,0x5d889db2adedf96dfce7,0xfa22afa7d52e2442130,0x5f86ca7ba6dea6a8e893,0x9c5099a52859176d4752,0xd50fe6990a22e18dd4b0],
[0x2ed6fb43c8bba8f0af14,0xd8ba08696327b6012ea0,0x4ceaf38c58a237944168,0x1341a77d2d4206f5c94f,0xf184c8fd0a70c64e91e,0xf64407d470f5bcce9030,0x71dbba9bd5d2cc1c395b,0x289a7fa2f6fc6013821,0xf4ef373225648a0edc6f,0x6c04f4b171ba3389ff14,0xca26c8920e9c037660f0,0x3c2368175db81094766e,0xc7a103306755b7d35668,0x90166598e5e40587ef50,0x6536276a74e11d786a01,0xb6737d6eec47d9660b0b,0xe8b48b8c016f8e372a18,0xb6b7271b1e1fec40164,0x3575325917c793590668,0x112fedee56468ea9592f,0xc76b3e662643d93cde37,0xbe8bd3cb7c0cef7312d0,0xa2e078cdd1fe83378d84,0x7cd0e65373dd88bbe3e6],
[0x65069a285ea4206bbd27,0xe27bdc30da21373b3765,0xcf4551803695b1d6720c,0x1e076deffca3de3d8556,0x9fe830c1b6158500e36,0x79b4dbb70a2421545276,0x31e723d85a47d4348730,0x9b897cf1d398875251c0,0xde06eeeed4aafacdd6cb,0x935d406cc60ce905e012,0xcf39548c12ed87886773,0xb4aba002db26eadf8fd,0x724e84754ef968cf8e7b,0x4e90ce080a3e88e6cf90,0xaae799895140e9f8b302,0xfddf837fd32d980ce465,0xb8aebecdc5f6a4c2db36,0x93f4d6ff1fb7e1f885d7,0x7fe88ea96c3e928940e6,0x4c0ea0f6f7f33f504bcd,0x6b1ca01725568fa9ebea,0xa65081425a763da7c098,0x35bccc17f91555102c5f,0xeddbe1912295da8cc0c1],
[0xe1868064a1d08ff75ac5,0xd2d3a9b5844d5b1e1f53,0x510687a721614c60cf1c,0x3789d5040ce272524f77,0x4e87ccfd113c551d904,0x7b9f03d51a4bd74328f2,0x73f8c2435d8e9e0b8dcb,0x4d17290e02144e6614b3,0xab6ac185b96195bc2d40,0x8f1a86c174055ffec731,0x2a0ed6f86832fb506060,0xc23df3184f02898082c0,0xf283d4942ac05bfb6f8d,0x7dcce3c54ddb11a0aab9,0xb321b4c31a0da6366ffe,0x47f7f8cc35716df3a7ad,0xd33fc0264291691c75f,0xf6ac28bfc4f904655e5d,0x15c587b2b56c7e43becc,0x72e9154aa0e5d0368937,0x4e5b6bf587fbdb525a0f,0x74bb3b91662fddf98c63,0x8101b06809990119fc74,0xf70af248849bb6a37944],
[0x81511ef7b4aece035ef3,0x1a107046c0408824b292,0xc44e2e28a2c9f33d705f,0x8e8b4d0f1ddf0cc49e79,0x6b18694164b879fa602d,0x2e1607953a419c0dd1bd,0xb31066b1cc7a70d9d915,0x717a44aa8c3a8e202711,0x476d5be6dbfeee393b89,0xbe6bbb3a9c30a67d511a,0xa08ea4d1d22d50bcf291,0x9aa35668c3a978b448cd,0x38fe163383fbf4c62da5,0x66bf967223e9fb5602f1,0xb3404921790ccc122159,0xec59e505738f9aa4c70e,0x998753ceb393f49a70fe,0xc5a0fad2167292543570,0xde6e0613a329c36a9db5,0xc9b9c4b345c89d53ff5c,0x195568bed51df336ddc5,0x59902dd9ff23619f798f,0x8023298454a4beb5f477,0x4c2d3b61ee1f66392f6e],
[0xac852dc4515f06d3126e,0xfece24a0f0748c6377c2,0x17da06907a841e6747f0,0xb74e465a9fa3f178d547,0x63cb9f655b8b0ee3868,0x32710c3cf211fc28a6b,0x8cb0eea5b0cfc15e6865,0x9ab0de590e6dd2cbc946,0x3c88f1c3358b3fb3231,0xec05fbe9ccba3ceb2d15,0x72ef97fb7347602e6965,0xc390bcd473fe3bea5002,0x6d316e7e4b360836f92c,0x1aacad74dac9b3f42729,0x67d5fa0022883d6c7ffe,0x3e835c780f18248820c4,0xe70e3a3335563278419,0x8210143695edad525330,0x1c6acbf2d35be9f2bd5e,0xfa5ba10e7347a46c5d9d,0x87467d88dc3cd45d3746,0x7a4b8f8fa8e1c5599b94,0xb30af9e37148121138b9,0xd4a427c7d9640082b447],
[0x71d18cde8044e269f9c4,0xcd7ec183f630e7997085,0x1d5dbe6a0e8ca0d65d64,0x6d6c2b24b2234a22654,0x9c118ff9ab62129ebe3,0xd3b4e7cf5b93a85b08fb,0xe2e58ba7e60d5eaf95c5,0xb0b2dc88d7c41366d6f2,0x27afd6ada6312e434842,0x4ae568da6479a73615af,0xc524ea2c355def617126,0x902336f4580d2047e46e,0xc4e23c468179d43555e0,0x4c75add0cea83d4c7c3d,0x754d5aec2b2379fc1872,0xbfce27ef99204da51333,0x67b1e9228b71089583c3,0xf603fb944eb0fec3161e,0x92d2d054acf249896908,0x8ce9b1bde53fe7b0d438,0x31c7c2ff254bfa46ff69,0x42e7f2903dd0b26ec810,0x6d1e2fabd51ec5e4de5c,0xc6dc7f3b3687ccf81375],
[0x7ad03130d8de9ac39aa2,0xb9dd5459eecb6fd6abf8,0xb3c85632613c93936503,0xfeaa67d43786f71a8fbb,0xa9efed981dddceef48ec,0x4cce863fb138789c5ac8,0xcbc704cac7af319687cc,0x7ba369924a34e5be2ab3,0x8d5f26397ace45c8cc68,0xccbc0bd40aa06812f2c0,0xc3e8c0660e42329bf9e2,0x4c2fc3b1134e7ef8fb7a,0x84c170d3db01474761ba,0x902b91fd8e454685e8a3,0x1849c5eee903bf2bbe71,0xbdd901f87e0c36ff7b3d,0x87282484067496530c8d,0xa1b28bb178f2a15702c5,0x48310bb9c897e9f14f10,0xe550623b3530238c6d87,0xbd4fa2a7e9a6879d0943,0x647e25b825f980611f24,0x9ecf277726e741b0fd47,0x1987f09e6e84f18193ec],
[0x587d0347761c97cfb823,0xfd0c4bb88bcbcc2f6d90,0xfe08b208334a8e9f51e7,0x7ed5d0412e923a8c083f,0xf4c57efdf53e36323acc,0x29a2d711c040e0b21c23,0x4128985e3a95adfeecc8,0xffd8b97adfc5fcc1fd9e,0x16fc959de98e6462233f,0xe766b54bda4a301d1b24,0x996ad8f619cc0c321338,0x624b93a481c680e5a1de,0x3fa6fed9ceb233101514,0x1fd1ddb2360ec4780169,0xf3be1311c26087e667bd,0x3a248f2b0c99c4a56778,0xaa48860edaff6d15f54,0x220a019adf77e3567682,0xe24bbabaacca2cc50872,0xdd40cb8feac8b4effedf,0xcc01cfe53ba240f507d7,0xd91038b1e81ff88e1be3,0x94a56692b94f2c951b4b,0x82f16dc0616ffb482fdc],
[0x39dcca85bd427c19eb10,0x47b9ce33b01c14e5d8bb,0x775748abd45ffff0681b,0xcdd576c676823fed1b91,0x2afc0f9915e6c886eac5,0x5f2dc660c947390501e0,0xd7b952615c079baaa9e,0xe746fe5ff2a2ce388757,0xfb16f87d560fb1ca6e1a,0xd22e3d8ffb0ce7a51705,0xe00c1df8404cefb242a2,0x9c5cb4977af818b6cedc,0x2ae4033846a73bf399fe,0x7ff9cbcb83c8211a01ee,0xa08a4cd2d18b4f79dbbb,0x58a86e524c5b3aaf916a,0x1c09a065bb0e2a5b4adb,0x7e3dd3b8d73f300a855d,0x1b4c26bb55b9ae1c30a2,0x2db65f18e134fed243c9,0xde706ce9cea4c9008707,0x60042465d73d65e9890,0x77b129d337117924ab3f,0xd6e6e92f53bc9cbc40f0]]

def tile11 : List (List Nat) :=
[[0xd344c58863e16c05cb5b,0x624d475d69682a5b9320,0x5bd77f494143644ef904,0x835b2265aed8d9901bdb,0x2d8a7cc28a9ba31cecc,0x8a43c52ea45070e988bb,0xe42c78987460ce4a6f78,0xd271b4eacf9b0821dca4,0x54b21f84ad1671817648,0x7dd418c64a19a1d685c7,0x535f676e81d832c4e502,0xecdf1041a4d001ea8c01,0x89935a3b05f24c7fc084,0xe3839f50a2a6f27e5f08,0xec08e9bdfa8396fb6253,0x79dbda699ed9d3a1fbcb,0x8a64023664f15aa9d301,0xa3f00c78130313cacb13,0x414e875171dbb7e31123,0xe64ab22e0d1cae7c921b,0x9039e39daf8109497f64,0x5ca051ca86faa7520f2f,0xd3e760805ef542952179,0xe6d27649ce8d2996057a],
[0xc623416248ab2300d9c,0x4feaf53bf966e6ac3016,0xaf349e3dbd4062ecb05d,0x83b5e620fe9b55932f5d,0x34cb35c8aeb910688b52,0x93da90d3a8db7f3b240f,0x344c4b545b66ca02df4f,0x32119ff2c4f57378f7fc,0x389f15ab423b26050b4a,0x3bb7b7f11760efe9de3a,0xa25564a383393b621844,0x57069f2a594303194a03,0xf860a9206e5596b58bb7,0x99c9e40f69fc430e8846,0xe0522f0e75042d515b9c,0xde6741696208c3a7a7c4,0x1dcafa6c48726eba202d,0xaee1679056254301e437,0x760577db2e9adbb4369e,0xbb9b3a954c26448f1d08,0x7fbdc826b39f84272926,0x668023d1abbc2892ce7b,0xfabe66011ee0c31b3f92,0x4310d544920d333e831b],
[0xc07967530f41b64fbc0e,0x3694b9c0c5853af653e,0x13a2c5be643ae988bd82,0xd9d340a9cc49be542f5c,0x1bca9984a8d04d9d15c6,0xb37342840b5ce4563dee,0x5c0f9aa7e23bdfcff2d3,0xd9d83d8fab07366875dc,0xf33dfe500cc15eab7fab,0x4e87c88f86290ae4638d,0x7f5136f1584947793085,0x34e599ecd9f4624ed7d1,0x3de3087ff3eead9bb9e,0x4ebdfca1f7543cfa7ed2,0x8ab737023aced6be954b,0xc0f030172d22b9a98a46,0xa16facd9f2f485b9c09f,0xbaf875aa4beef4331341,0x165154fc2069de9727a1,0x37304189c62e0ae8c87,0x6d9f8379858e5c043460,0xeced8a50d91d5d70bf9e,0x85aada9e30eef1959a86,0x6d28284f7a448ecb87cb],
[0xc77302c012a0df011a5d,0x99fde9cda99405af43b3,0x75d9e16ed63aa1ef1d03,0x27d68a8e8ccb0dddb597,0x5045e5014d09297f8ce3,0x312c53bcf3946dfcc1da,0x88a7c4ddaf1d181bf543,0x885c976ab354c1b00a79,0xc4eb602d974a33feaea5,0x5171666f88a18af6247,0x8e85be9ac8eff1c1d306,0xdc1b9ff91885a905675c,0xc3fe5323e8131f52c41,0x89a2b8062ecbc5fdf040,0x7b9f094efe4bf1fd870,0x656768b456ded652d2a4,0x99ac5c9c58d8ab29b065,0xd425c9bf2a413646f4cc,0x318b8ba898e0415a4ec,0x81cc7f3ce6df408cdfae,0x6e82430197768b083671,0x1c83e5f6899d9379d855,0xc0df9ec051711a08c9de,0xf1708fa24040ce297204],
[0xfd18e7de16ed68ef5f13,0x7071565291fcbcd4f71d,0xa4c12dc8c67f04e2b1a9,0x559ca34c65814e8de172,0x80fd06432a49de0dfb15,0x81d22821d10f16fb2d60,0x712d798dbcaab684ce6c,0xe49d9ee99dc7c2a03c93,0x1ee9387b11dca26d2278,0x1728eb70a411c429f37c,0x92f674db652c3dc524ce,0x756e7bbb0b48bf1443ac,0x5a26ad15c4b79678c4ac,0xc8b92c9ccc365a8a080b,0xca6422a1ec7ba2690d03,0x8f5e9f314bb0956aea9e,0xd5e531588da9f801dbb6,0x76045b7220010eae5547,0xff9db11e2d8a7db57a2d,0xb178a54dc83e0fafbdc8,0x99c0e1360b6427a8eed0,0x6f8a1d6fc942855e2f06,0xf27e74f47961ed82c4e2,0xda6a706bf3be2acc7a6e],
[0x44d004ba672f0e234a4e,0x4275e455389c264e67d1,0xbbcd9998c532358b4610,0x5932eee940f544fac4e3,0x600fb00d50898354c49d,0x84425bfdf788f8c0e8b4,0x3f679f496f10183eb391,0x2918e043639e41c2da4b,0x7f07690fe89f8efc4125,0x2dd1af773abec622db1c,0x87604fde47e56c8c2af3,0x99d761942689aa1ff7b1,0x1f5b57398b82a0ce152b,0xb631e4b735f41b22013b,0xc5c04724f0aeac8ec774,0xf4bfd2294ba573e87cc7,0xe9f1f664da8740c7a693,0x148f6eaf0de0f056efeb,0xad065acb541113e0360b,0x1eace5f69bfc80690825,0x69b306c8dedfd462e906,0xc5909937b8ba6fd4af3a,0xdf2180584db29e23ed3,0xc6525508201e577301a],
[0x8ccbe046f31d01654da6,0x490fae9137cd9af1aab2,0x6627b027dd2ebe203712,0x450961741c21f3b1125,0x536c4520fb5f377f5f27,0x497971402bfd922beb4a,0x136a5bab8c259463953e,0x630812275bf0428f2632,0x1875404ced373993d19,0xab8009ac48bfbacc34d8,0x47f66c8729fc2997702f,0x79ef0940cbc8979fb714,0x1fe8a7e3bd66fe586282,0x9bfecd418d5cad8273f3,0x7f136d5d1e936d5ec80b,0xdd05143b28a74d3e6d83,0xa398f016ee339d8e6abe,0xb06c7496ffed42eb8de9,0xcf45f677633f7cd83adb,0xcdcc2e06a9bcd259f6ce,0xdf5784af142d85fd8438,0xc3a8e1bb480e126aeb3e,0x7c99652b280309746cb9,0xe86067b681c0d3aedc12],
[0x8407b8e1b79acdaeb2fa,0xeeb66374cf2ab1cdcda9,0x57b6c141eaa009923c6f,0xe142cae9b407c0064356,0x4a5fc2f4d615ff7b038c,0x22557ea3dc3b57d07b54,0xee4bb46e5ac1345bd8e5,0xc629e26122c43449e19b,0x999d6141a3d3b3e0db6d,0xd56bdb6d8ec38ff9ee32,0xf6f3b6acf5a938ee82d,0x70383b4bf937759aaab9,0x32f188313ad005983b45,0x2b8cf463ffc462715b68,0x8d18d22d3a5015d8d22e,0x3192164520c87501310,0x6549aff5eabdcd1cbb14,0xb3d5a6d755aa21ec5742,0xe9ba87f0d0930dbc4b21,0x3f7236d8f6515ae4b1a2,0x89fbd4e6858ea16f98e0,0x2873e2a129ffb305af25,0x51cf5ed1454c4a64f6a,0x7426d87362dd37ae658a],
[0x347148d21a87404fb30d,0x8e7ada8a2267cf90bb43,0x1b637dc8c5964c6ced96,0x9c6e59b9662764bf4ec9,0x64263f90a8dce4fc3217,0x5fb9698963e4a1ea1bb5,0xe6ad38434abfa97c66a8,0x246d93d0b3691f12a4f1,0x75fd655f8f9adf42fffd,0xf970e23eb9c98b05d00b,0x6944615f86b8b5d9513b,0xfeadad431b9d97a1945,0xc827756f6e2f93b88000,0x47143b9f5dabba1cc251,0xa659c41d99dabe7ed192,0x280af4a184bdc56d5dfc,0xd2decaf7339bc024dd72,0x54925542abe3d723f6cf,0x16bb228c4348e7743f4d,0x9403d0015472ba724fad,0xc553274c6000456da00f,0x1a961c54ff5ad72c4598,0x9bd8e9b3e62cf2e52c98,0x208c28c4d1a63bbecdcc],
[0x694a368439d3f84b0ff9,0x23401c17d6a11a697c9f,0xe737d02260fc7f6b7c34,0x450cc51d90044f8b1f61,0xd2ff6a6b8a3be9d64b06,0xed807ee5b340cd0936a4,0x6ac774903b96951a7c7c,0x3b67decb2ca29920ea14,0xc17653c28467e30a91ff,0x9d9c8c81b40b03b673ba,0x5ba252f2b6bed93989d6,0x822b1577618c1d479eb3,0x63e2121e40e7604c97d9,0x4457c04a49f8b192e346,0xdd6959264d65acfea0d3,0x9a101cf0d41e997c292d,0x29141e95f80179cb9b7f,0x22547ccc147e9c7d5700,0xebf699ef82ac64f91d18,0x32ae109fdaef8cd250ff,0x221c739e3642bf48e0c6,0xaf7c9ee14e703a95a2fd,0x5eb36a2d263a3346cfd7,0x16415b248c62ec48a76f],
[0xa8db0e20b94bbefc7702,0x14eeba94c70d63d63aec,0xe7d01f78e70aba7e5150,0xead135fbfb5e2266844,0x6873f4f7c7d661f2c2f9,0x86e613fa45a8ef0dfc93,0x1e3aab8384a49db655fc,0x599d8e5d2da0d31b7777,0xa41a571a513d8e2e2f01,0xa9cf83aa9613641a1c77,0x795f0ffe1cc9b34147d2,0xbc06e9d45e780c273e98,0x1dce549adf9336b1fe9b,0xf930a0aa6b066cb30144,0x98e76e79c4f1278f5037,0x5c014ad10915d92166a4,0x7dfde86bbc0542e1c35a,0x7e6cb65e923f413bdb02,0xe72c1fed21eeed3fa831,0x47a1c71084d6e78385c1,0xb9778b675d443e784893,0x35e191994de669a8096f,0xfa6154ec1723619923,0x4950a1750e42e24dbcff],
[0x5e5cfde3f77fbf41a147,0x6084935ade94c29bb342,0xc5f3766dfa3a748f5a05,0xd9f6dc2164b81c7f2b00,0xae8a07dbe542340621fd,0x4e4d0d1f4ca87cc8f9a6,0x1e4f02beb1e7cc5824fe,0x67c2f87cc8666d6ac812,0x9d8b5dcaf04ad3d3438f,0xac0cb373994fe46c0302,0x8e9f5dd7e95160bdcff1,0xefb1940721c2b5a06d58,0x278e9447a70a2d1002ec,0x7c0d1538fe293c6ce121,0x7e3e9e7131c88e2ab9f2,0x71107b61c51e746f4035,0x9d03292a44683c67a526,0x95720376977f1b20f944,0x2927b5ceec4a3126911c,0x67fecde6e2c2ee6c4d81,0xe3df238aa958a226ea6,0x9b6fcda008695196fdb6,0x58c02ea5546446fcb682,0x6d0211f548421058ddba],
[0xee79ad97763d25ec07ee,0xb95a623e1b90e348b605,0x8a8f8ac3e9e9a2d37b2,0x65b43908b2946876f9b1,0xe790500bc2a6874bd7ba,0x99cbedfdff7658347167,0x70c63561e1fd55d9c06d,0x22bf1d7ece072bf783b6,0xf745143e0a02ee4b6e41,0xf104af46ea5d03527605,0x42cdaa3b746d1e505c9d,0x9a72af16aa5ed92c185b,0x26df5e2a27d44487b43b,0x1f530bf674bc358df2f6,0x331892630d071a684f3b,0xe259919d352502c9c53d,0x30a26609d5b36980c39a,0x1d72fe57cb0f824abff8,0x4803d834aac0e5d9f5ec,0x476c7a52a5d364ed5d9d,0x9222afce129430d1fc6,0x860843d817cdb9f92537,0xb59a03e6ba74d47f2e1b,0x383de6f1bdf1b6b4844d],
[0x9837f04e911cbb00c8d4,0x24d570b1ced61406edaa,0x8d38502a848ec351a645,0x23558dc546506f45194a,0x3cdd437e1cb5f3938aa9,0x8e2aab4f27a2c8335235,0x37526a99ee001cfd4234,0x354fc9dc125a3bd6c421,0x2af8de71388f52b78601,0xa5ef48c969d67da3406,0x53c0902b984473056e28,0xa0d40e36cc78582a9c18,0x9f53ce7e00dd70dbf7f2,0xf2ea18424acb027e83d1,0x7d3b1118a39e97c2890e,0xad3426564ec2ad2a899e,0xd2da2e45c2d69186076,0x9c3c5f41157cc46627e6,0x27e4924764e92b8ab3e6,0xf13be8b2bb033cabe90a,0x8b00cf2d99e9f049ca2d,0x5e70e2b950bf3dbc7af6,0x6c0b7c0d7824278e0296,0xea4bf5fd1550af438da2],
[0x19b3fbf753330e7d13ff,0xbe64dc3f8bde2c65e92b,0x6221f3d430e624233721,0xba8f19b7d3f5ef547685,0x209061cf15ef6552e825,0x3e26dbe6c813983fb310,0x67547ce9021794e502a0,0x881c24a7c25e1b696af7,0xfd4cc84b2ab39d7e3123,0x470746d59e85e3c04605,0x64e2e588c1ad51b5bad4,0x8e98360586c24671b087,0x168279ee88bfe3621614,0x41459a7b7a0bd1e0ce41,0x764269174787a6256a93,0x1912570a89aad3d64ade,0xcae3005f43175b33ec96,0xed5af2ff19ac95cc08a1,0x6de89487a896f67a8f6f,0xebd182d0723dcfdb3d7c,0x897bd602dbe25a4990c2,0x835e8c08512232f30189,0xef384fc8c6049bd47b46,0xd425f2f32b85bcbdcddc],
[0x3b0d3d7e0d37bf414e2,0x12c54cbb991d73fa4623,0x6220f483ab7669790a36,0xe4f162e33c6066258939,0xc4f9ad79291eb69f8c3a,0xe5c359dc126611143599,0x7cf72490e452402a9269,0x51e4fa81f783fccf2396,0x53240ca1270bfb8623ff,0x48d2b1f6ba3e2a43b9b5,0xbf73352ebf636ef596be,0x8a4949c17112721d154e,0xa2849907adaf0db8b1ec,0x7779dd77ffeebf87c53b,0x44c3118bc373935ee95d,0x27576bcd951fccaecbbb,0x6484fc927175be656758,0xe7bc51b27bbdab345427,0x8f0b59509b24ab627aff,0x6692f4d1c115e96b6691,0xcebd9aff196678506e99,0xfd83b4bbec3ca3bcdd6f,0x34c5627b7c0a288c887f,0x3947ed311a589cd8057a]]

def tile12 : List (List Nat) :=
[[0x21d639f45ab828ee876,0x4d96694f0d3b5a87d644,0x2c98068d268dc3070599,0x8998c3bf092e3c265363,0x4e80f9149473c4ef900a,0x6eeffbc05eb71b4b6a66,0x77136dcbdc47e103a967,0xdc8267c6a9bcf12ff8f0,0xfaab967d9732b743c3a1,0x42bce0e20700d6a45030,0x11001afd27cd3bfd704,0xe8e314b071993c2b01c6,0xa69bf91aac47171598d2,0xd604d6faf30e1f0aa235,0x217f40aa4da4c1ca3c2,0x285bcc3fd8a8581d5,0xfe7beceaec94ffcd1b49,0xd3baa61c0657d76b6b9c,0x8da10ab58674b235a37f,0x9b7e1e94e980671f9308,0xcaad22126b53fca7f4f,0x901c7f5b5df8858ff33d,0xff16195cd2631b9b12e4,0x8ff30b841bc1f4aff36d],
[0xf1cd62488aabb438352e,0x53f8693ab3ba00c2651f,0xead05b8d5852325d1330,0xcf789af080a172073f8e,0x1759cbbc7dfb17e5b6f2,0xb6a6ccd98d217e9d14be,0x22f6d71aa67aae1c57ab,0xc191270073dc25508b7c,0xf327b618744c29dad74c,0x78d8967af4759aaacd64,0x48e041a27154f073d65a,0x3b60bc53c80171aad4ed,0xce373fd87aa79925ceed,0xa8e1c084258018d404d4,0xf1853cd7b816dcd63391,0xf353cf0838b58041c264,0xc8ef550e8e0a226bcd9a,0xd0ca4b2d5ead65fbce4c,0xffec9026839e29c80fb1,0xd34bdcc17684cfd1c9de,0xfb27d23400104c1f0896,0xcaf1edccc1d3d4426715,0xbfec50000b88426d3b87,0x24fbac954f7d717ff70d],
[0x60c71e9b8b2895b1baa3,0x11bfcd3bdad7695f8759,0x7ad93234fdd785340c65,0x97ffe409f0558245599,0x210b399682f105ae3ed7,0xb93a1c8732486fe5af71,0xfd5b07a72611d89c16db,0xd9ac0f01cbedde00a4e3,0xba706872c050ae56f51,0xb74d09d052e3819fda5f,0x7b94aecef5b2495cecd5,0x187d4944dcacb6204579,0xbb82c654e8f649b4b140,0x5c9ac64a9db784ece3fd,0x88adb4855b601bcd3420,0x9ebf2e9a1b1ddfcb85d6,0xa24082b3eb8e5801534c,0x7d3bf1e715adf16cf9c4,0x78b5b2bf24a114389531,0x23ffe4db6acea4ad6279,0x7b8957d87e9c27bc32cf,0x8884a80d2809326f065f,0xb786fc732a8cc28858ca,0x78942d2d29f1418a1b19],
[0xac2cd1d43ab1843d4611,0xb7160e00054041fe48a3,0xb37d12644017c8d39a83,0x4225d5c73b69f00080a5,0x17236d86bf9c975e3099,0xb656ef1d8ec88d4408eb,0x48f680a3195b409da46e,0xf79ceabbd79281b6292,0xab6f40247efbcdcb7a23,0xf74f70dbeae5cc29714a,0x4b3a7688eb841bfaa8ce,0x3663717cdbcfec9a7a5b,0xc99f6b1ec89b5dd54cdd,0x9832197bd14c10b3c463,0x6102d62de85249e98ba3,0xdaf5e7fa5ccaba3e1911,0xc103d1a39eb500a588c7,0xa8f5542a9167de95ff74,0xe70b4d686dcb2cc7c1a0,0x128297c55d067700400d,0x19989167a11589a46ac,0x3565032523afe33a5a57,0xca948e226998d8239433,0x149e1e1ced3367fc635e],
[0x72ed35c8f4e8cbd2675c,0xd969e9c7a61a5a5d92d8,0xf456ebb55044b493b80d,0x891b107bc46df0a6eefd,0xf7777876735076e90878,0xe83554ecc6ea5acd4c5a,0x74c40c3bfa8c4a18266d,0x9b2867d6a9455a63449e,0xe8140b3189a47c91b471,0xe551576a4183481abf56,0xd491c3d33b6332262887,0xd0f9d303020f2dc943c,0x22d0ffbd53434758a92,0x9b72a666f7c3b9d91b69,0xe4d0393311009a067e45,0x51a317e7e9f01b973d1a,0x3334726edee2d968e9f4,0x303d649146216d47dded,0x59a6181c61ca393bb72e,0xb9b1d1acce712472609e,0x304be6ce84efdbbeb40a,0x791e944eb46ab63893bf,0xe1b3db1f08d28336916e,0xddca95b7f1925c26980e],
[0x14a201f449ed8991d0d6,0x5a461c4008775c00eab9,0x17ac329600920039b870,0x79c7ac8aec595ad80248,0x5f661bcdb20678e50a70,0x83e100c013ff206fc4c,0x65918aff76ccbb8c7bbf,0xd9cf50f792d190428788,0xb0d268c7356b82ae953c,0xa8874ba2ffe92fcff2f8,0xb678eda948e2ada36e1b,0x93528b6351442ba469a7,0x3d52e244b961af6c4e94,0x52d8504b502ee2fd49c9,0x6c45952b3c35f4d8191a,0x488c2e35f91f4468c31c,0x4e2b0d08fa010939a5d9,0xae58822b4092cedfaa88,0x882170531c2f0d390778,0xf5ab18070be0d74e3939,0x3f55e22d2e5edd367524,0xf88712741e541acf5948,0x5d5a3a35d8ccceee66fe,0x6871e64f1eccdbf04026],
[0x4aa3ab504c9d3c36dcee,0x7a32a0d06b2884d4e005,0x7c9786ab1745a1c2f5fc,0x1314fb0e1e872a6ad9bd,0x2c541e868899ba339fe8,0xb8fc7803143b6f15352d,0x375d99acb24992af6309,0x81e2973b598543efc589,0x422baff7f5d14eb24795,0xc52b5ff6539af222232b,0x76a3bbf897fbe62c8a2c,0x28a0933cb1fb2169abe5,0x57cf2bb5e8e6b1b35c,0x8c32c14fd6ba53ee8da8,0xedf1ad9d13b7fdce4220,0xc97f4933064be1a09d98,0xe64183096f6933546a1,0x2576834f058b155b326,0xc176bd35f54350cbe8e8,0xe53b2b95470fd1d9c754,0xb706bf25dba89de1cb6c,0xda2672be6259f0287216,0xdb9c7116712d17576238,0xde7f245b28323c192ca7],
[0xf88783876bc0c0c06af8,0x6c3519433c829af7e4ed,0x5684d42e37c1ac822ad8,0x2e544ff266eea98fd992,0x4e2f8a6c3b4cf244d8a2,0xb28e5d37bf0ae758e5b2,0x51d83139b4c18f91225f,0x9e08fbd57c21ba640e60,0xc86372af5d0c66ef154,0x5f46f7e1c40c154faa96,0x235071e92b24b2184532,0xb5b646aff47742b3013d,0x82c4b576441fba1e68c5,0x6301c90912ef86ce86b9,0xa4737bbb7e9ed5d140,0x8ed13a48a9939862f319,0xcc8e6a976c4cd2ec4b48,0xba7e4b01994491c2f2b5,0xadb108278e9e06548fb5,0x302e45cd9d2e10e88f8f,0x756bc8ca65a5f33b086b,0x6e94567df314283ea3fb,0x857a24e36ec4108b21b3,0x30695ffe89a8bc9cf3ae],
[0x6da106fa05d47c384893,0x23d4db756e0c659c177f,0x187abc0fef3043d82328,0x6acf2569a2ae651be846,0x2de34a5c15b530529be9,0xb6390332c1faa9396eb7,0xa647d3773261c51d4e,0xa4583595331c7288d0db,0x4e3b99c1145a4dc8761e,0x61e608eb9d9ef2e8cb8b,0x1a616379150db11a497a,0x59d5a9d4f4f184ed0b14,0x487438e71f31b2283091,0xc6f97a6abf62ed45325a,0x26fdc23be3faa44ab31b,0xa2e080e6fd5751d01124,0x810aaf598763696be7c3,0x4b9b97c52dc43b7e7382,0x76d90aeabfd943a4899,0x27c6214d071372c76216,0x41fdd9888eea0989c67,0x989260495595005f0172,0x443561c22e32b1712e49,0xcddf4885911fb245ca3],
[0xc75a1c8b06be52bc2fb4,0xd81c5589a63dd460de6e,0x85a8ad798be22ca1545c,0xe61f6274e95835acf866,0xaa895a6cfc45e28c6a8,0xe1b69ecefee26ff950f,0x29d2dd28ab8b8c3183e2,0x4c3fd7cb0fe19b8bb5cf,0x65a9a5bb105a4d69d07f,0x9f1bdc742f0c61641305,0x7aa95b3390ba4b172b4f,0x20516f5248681b24d5ac,0xf3eae561c8c38cc73f89,0x2cac01ffead8d72608fa,0x971c9b7a09ab9a535f7,0x4aebc1d3d5d91e698c7d,0x66f22f14575f78f6fbcd,0x259e3a68b0c37c58b39f,0x8363e83ba8d052922ccb,0x91c08efb146bcfa331c5,0x8361c992c9c23c13cb20,0x461efb1de22a153ef3a1,0x823fc9ba90c28630d2af,0xb1c3043dae2e62e56a73],
[0x13983b0b71e2e50bfca8,0xff80a4d5bc023e08f56b,0x7667835e58c241ac20ff,0xfa5daa5ccea4ee8e0369,0xecdc9de2b6f3f6af88d6,0x6506d3d7c5d16d74d055,0x88d2fa460ce5023b0a0a,0x89eee779aa3c0540706,0x6acc00aa8b3a501ce2e1,0xf44d948a7bd9856100da,0xc13a4ca327416751b3cc,0xd915908436a873e910e0,0x49e50182a1e7718186cc,0x9a7b8866ce1921b4ea34,0x9747d5dddac8a5ad5b4d,0x4c92791e9fda3fb279b0,0xf492fe61c725ebeb897,0x7281705408e09f2cdcd7,0xc014a645f2349bc24eb0,0xb459dc2bae5f9a173c2d,0x885cd3bc6b82fc09083a,0x64e890222fbb48047f4,0x4a56d2c97f04532a0ea0,0xe5efd2a60392a2569781],
[0x9a9a3ec35e732e954528,0xf857fa9c9f3517cf7735,0xfdf194897be584c26c4e,0x6eb6c32e59ab64c40145,0xe0e445c5345a33630055,0x2b595e54fa0aa8a30a07,0x4d3d9f74b062e67b97f8,0xb6f99d8f48256958b53c,0xa636d10ec47c240393e,0xd16e7ef77b73c552e1b8,0xd7d3941d1d9d687f5c26,0xf2abaec201c75e3d1724,0x3b9d6c14c2b1aa9d0d5e,0x98e58a1b24de0a7ff456,0x71b0fa99463dd29e99df,0x158876ad8f67db66a789,0xb749d919d97cf68662e,0x2f0082928ee457eb68ad,0x87d2db09c8a29583cef7,0xccbfd72007ab747e2bd4,0xda331908ebf4be53ad7d,0x36c55969be1b84104919,0xbc7e286e1fc2f1f2c859,0xf5392fe0263e4c9e573b],
[0x8c75023810fafa385c,0xa1a4683a01feb939245d,0x67d854f12da064c4e721,0xa775bc408074d773a1b5,0xed32a56bcc73f77f2581,0xac19473f5d76b01918d,0xcfd91bf74dcd8d3d021a,0x5fb12918ec1399c29773,0xfa33ceb1f105e3c0baa8,0x13fc04bb45b79b4fe88e,0xf3f1b8620c676e344680,0x712b92f267a89c9be9d2,0x8da28b606f42d21572fc,0x9fa391f9645107597651,0x7f8ef922a281036b25e5,0xe5979398f6452d7afbf8,0xbb4d1f1cd87c532e0e53,0x8c0e74bfe8e87d1abe64,0xe2a590da723aa39baab7,0xed5b096a09da7557ba6b,0x7f86f0fc64a711433082,0xeb39721d05a8ed94fa63,0x7be14d7e5fdabf890bb6,0xaa0226725e9b2a001a34],
[0x468761f65be2fc722351,0x163e2b57038ba9f28340,0x19833e392752b1649314,0xcb9f0a8699b39df462e1,0xa022810b76a195a3538,0x1e66d09f96b06655dd01,0x93e9166df67f9993f259,0x2e5c024d229eee076b90,0x22024102e9b8c62ce1d2,0x9c12ef574a5edcd134,0xe70aea66f1b3149a52fd,0x503cb5f54b6649da19d,0x2596876ecc483e30e744,0x16e9dddd759b64988b91,0x9a7afc45a0cbcececcc9,0x77b753cbcdd352dfdd8c,0x9d5855f61c6f9b945916,0xbdbcea9e878420c4399,0x63b957e15ec4a4d10094,0xbf8b111831dc5d9dd351,0x299d74a92d2744048076,0x1ea11db71fef40e5351e,0xa29c5561e3c8e35d7758,0x648818fc92077507ca2a],
[0x1122e17c932fd1355420,0x2e6771ab5175048a9a7b,0x7fa776c69b448a21f74b,0xc6820ba7eaa191a77115,0xf09251e045c1179519a2,0xb05ff42617592bd37bfd,0x66c599c85257f2297359,0xc65f176a4f3e1b84c60c,0x312a823f10e9815e7a29,0x78c2de822f9228dad413,0x5dfbb03c282eb671a12,0x182b160f48b33ab29364,0x229c432513ab28801cc2,0xa35d5d14e6c10ae6b723,0x6ad9920968d78702c0fe,0xc54f3eba929b85ad98e,0xcd9ea8ce46d9043d1c29,0x7e9757580d8d432acf10,0xf02b973d4776d3f20f30,0x590851bc570efd64da58,0xa3579232d9ec72160917,0x8b30994d6baefc0aeef1,0x5d0ed3e375ac7607deba,0xd7c4b196a1b9c3a2c6a1],
[0xd424aacf150229f0f1a,0xbadeafce37bc47905bb1,0x1bd36beee3270b2e1ef6,0x5153aa9cc4c49a010e8a,0x7d9c67df87887b8fd17e,0xcd34e5437f64bd6a0717,0x93f89c11f5c738c7b74c,0x2b912d08162cacda0a58,0x26cc3fe5c4a3792c6544,0x741a4130c2eef172f48b,0xe4a329d0db6428f84270,0xbeb88d62d300aca964c1,0x2bce0b129ac5284f1a3b,0x17282d42c18aef8d396a,0x4fac0d6e31d03b82785b,0x722d637f09e2bbd25809,0x826117d45735e030668a,0x734e574a56c607ac0adf,0x1c6b2c839293dd6ced76,0x52c60e10ecf125155177,0xa2e46675e138898e1406,0x9dc4aef8089940350211,0xaa2553ce919db16c919a,0xc1abec05e746328b5e53]]

def tile13 : List (List Nat) :=
[[0xa86fa3fe65d2e1fdd2d7,0x2345675c768677ab0830,0x39ba6bb887a5baeaddf6,0x3562f721f4ecbd9db132,0x13c37fc0dfc3e7109cc1,0xaa23761526690d6751b3,0x48bbf1da9621681d1f77,0x30ead756af065e0c14b4,0xcd361c8a62ea8ab69379,0x9e85384deec31a493a39,0x45f7e43a44eb82a81d2f,0xa793d998c3a12e1dd206,0xbe6b88b3d562ea6b96c1,0x40d672247cde171a5a61,0xb9d0a3eb1829bdc36745,0x32fd1f5858c3a1011634,0x4a163f8807e153182f9,0x40784fbd161acfe1762b,0x7ddb561a7c2d19847ab4,0xa0207d452b72b2e7c96b,0x229d03b271bde689d8b1,0x420de50f9dcd1caa98a1,0x63160007ecd180a9505d,0x659851cb6e3c053c1b89],
[0x42c720d25042e5761593,0x67f2d617ec2480120cd4,0xef3a821ae94c7ac598e1,0x1f4f93fb0c723995b574,0xfdd5ffec88e6fa08fefa,0x17760d29be0ad6333655,0xf27ad86133f55eebd0d5,0x7af03ad573b2c17bd339,0x39e0fba6f1354b0989ff,0xe8a591c88fd2b958b566,0x44c5ac1a84088083e852,0x2b4a8ec879e1d07a43a7,0x7b1daa21480d31ee361e,0x19b8f9e4dd2ee02e480e,0xcdfa5092479c01f4acc2,0xf031405f6e31bf9306a6,0x8a15d23264df1c948b76,0x7305a1a371cd94b05661,0xc08d40dfd417aa3001d7,0x69d057a49cf0c3453df4,0xf8bb2ee8f8eea4f40372,0xffdfbc8de76d413f1c90,0x67861af591513f2e3467,0xb5d884c3a0e578d4b523],
[0x5be135adf018f27efcac,0x2b7f79e781ba1126ab70,0x420312f98366e7661ec0,0xbb1f4d1304b1b455bd0e,0x2bda2fe3873220853aef,0xc224878c38d46968d015,0xfd5db1c41e3b963c33f4,0x16848f077c910d567bc9,0xac3ca2e87d754d8f0a7f,0x33013d7107ce8bbb6fba,0x848f5c4d1ba4ed333287,0xb9a112aaa3687dd0435f,0x7695f876c27a07fd4c7d,0x7849067078e89b7d0962,0x35c96a744f4b8911c8a9,0x681ea0bec007f29b2b72,0x7285326b754a6af233d4,0x3932119bf1594630a4cd,0x34775b9cc58f856e4810,0x127d94aefaff4ec822f2,0x352a3f8eb4ac24647392,0x2d66c6530f165a3eb64a,0x52a18184a3ed904cde50,0x81e5ef7a139cb20458d9],
[0x26c89da53931f5912781,0x95fddbacb2cec8f22310,0x3cfbe2b26a6f602484d9,0x4241f6f992958eb2e75e,0x91a0a34a6050650844af,0x57ca467801191e007894,0x1ac8cb485a061cc5c22e,0xe4a59c35db688371df46,0x840814811cb1aceb2574,0xebbb87cd61cd0db07a3e,0x54951ceb4378757dcd4c,0xdd4d24c21090b904893d,0x6b606d000408008e96b0,0x9cc1bccfe48b0f7fa9f6,0x865c954e166ba0f9c6a7,0xb194c595f709067931bd,0x3f4681aa1bbe811f739a,0xed03ab5bcf2a5d964004,0xcf9da082ca003389477a,0x4f4f0de8c1c680b3bfb6,0xe201c34da4e802292f71,0x187e8d1034e2cd79564,0xabb305a8eebaececd3bd,0x9f85131966bca45dcd06],
[0x7d5674c3230b3dcc3065,0xef6ba42c617c069c24d5,0x3fe0c758973a3525ed94,0xc2e7f34f2e244dd7f509,0x3b226e26b8f4e826c93c,0xddc586e83b4f629b2f91,0x495f7eee5fa291aed7d6,0x98a8fba57c864cff7677,0xa2c346a8c51942099b62,0xaa02b96c62805623d29e,0x83773922e4992d30a48f,0x9d0ea14e56dcff1db38f,0xfd0f5a01ee55a17f1e9,0xd4334cf36ccefb59ecef,0xcd072946dc5c77ebbe14,0xbf95a6b301f85e1d12a6,0x9572268f39fa79e008dd,0xb768e33a104605907120,0x8187429691f908bbea10,0x677e094e596f98d05bfc,0xf6f500804cca0084aed4,0x57430b016bc65a63a6f4,0x5aff9995bf75edf7df3c,0xf724052652ee2e852fc2],
[0x17ba4d0f5b7af8d59d49,0xf1236e856ac319e59c0,0x4d57ddc9abba626fec61,0x339ef7cc642d41544e73,0x22a0a18b6e795bb33587,0x7d99c9808e4d4e71290,0x501b73352546587c932,0xf336ca36731004fb5d45,0x43c6d2717889356feb48,0xa0a5e82fe5513fa098b,0x26c5930257d406b368d8,0x685c85f1c5f8e1f522dc,0xfbf324f50880a226f69e,0xd88dcc52d3b1d17d6ba6,0xf5246e29be44f83dab31,0x275207b7e14a4e7e7cdf,0x94813db1ac1e626b4a80,0x4a536d7d52146c44a7f6,0xb473e9fef14e9a4de187,0x9f4ef0613ddbb828b47d,0x73bb8380e47f26539189,0xfecf6175fb8e1b1e61a8,0xb046ae8b991b6dd6c47d,0x8eaea591f3208095afe1],
[0x11e2c01b1a11bb37180e,0x1b8a8699b36424fc0a75,0x1e7ca963fb7868ce843,0x4ae6f3f8db453aa0bf45,0x6865904bf8883e704b8e,0x4bfcb935cbe02c580cb1,0xa9cfea38f953ceee0063,0xba52db88ecfdbd45fbff,0xf48f14c644c0f292ee8c,0x1e73109163cab3a71386,0xf49647b429c97b57c905,0x74ac72ddf2eb6f75a022,0x9c720dc522d8a2c6faea,0x37133e4bfc384b153ca9,0x2540527ebb21a6d4215,0xd15b05985c319660b87b,0xcce25679718b3f84e393,0x8b203b92a0733a62ac3f,0xaa29ab7b8f0b9ac7d3b,0x73c7fe9507c04b288ae0,0x71dd4b37cfea6a8e838b,0x526f8e87416c2933062a,0x45a073522b8245d30962,0x72b7a3ee9387e37843f6],
[0x925937173bc01bc86190,0x45a44d0384de87003e8a,0x52fdd5c17c73761ac17b,0x257edfd24d5ce248096e,0x415464edc73064260d1b,0xe84b9598ada32a7f69d9,0xac336e93a2d0660f71ac,0xb0cd24e4e7775192a5cc,0x429addefc8396c5923f0,0xc8c2a976675da1383953,0xae5ddabcba6b8f65ff31,0x75268a5a71032da5f715,0x357e7e6aebf39777ef24,0xd5e169773fa24484c9f2,0xd80b0d0db29b46ce53be,0x10dc2fd89800cdb3804f,0x6a8e349fd713ac9645e4,0x1062cf6720285a21216e,0x90be2c809c6a7ba21cb6,0xc5f1cb2cce57d70117ba,0x46605e560307bd05163,0xd5d6eb073d5976c6405d,0x9ef64c9bcd566f9c4e2,0x603355e3bc7f49f09cc8],
[0xe7c02c91d34e50235c7,0x4c39572b158693db854c,0xfe2397dcebf7114d3128,0xa952d25e359aa95c9bdb,0xff51ac5d123cb3c00154,0xb75690132b793e461cb0,0x20ac3b0d704f62053628,0xac994f95221afdd8b2d5,0x6251681591acac722976,0x95fbb2d0ea201e9fe9b1,0x2644fb817a564ebd7e62,0xc88831ef27b2eff80cb4,0xa2da4c58c8b41ffea996,0xf02c766abdb9f2859cfb,0x9851cdc03e11810e7d45,0xe045b51942fbaaa3d2e3,0xc37adda5123743128032,0xcff526d2dc54068b29d6,0xb96499829f3ab6bea362,0x10f4a593243e60db6fc1,0x2b6219b8e40002dd059,0x1acedf00dce8f133438e,0x85dc1efc95d1d80b36b5,0xe6f80faa4cdcb05ecb66],
[0xe1930d9ca103b075ea49,0x3f49e37f69afad158110,0xc994bab1ea7102b71fe1,0xcd24da8105fbacdf7aa3,0x95c856c231784c7199e3,0xa5b7884884f9e85dee53,0x15cae725c98480ea0fd3,0x3884be312ecc0fd1a4c8,0x6419e142633002f5d18d,0x6a57977a14359725df88,0x5e012e7346f5461485ca,0x9dc899ead4ee1466176c,0xee5c8252656771239e6f,0x9556c0a9137337cdfb8f,0xe7b4dda4bfc07f0287a2,0x1b8991439b8951657b20,0x453d90f1bb71f0ee1cf5,0x958a5d35260b4c110b4a,0x6b028e19ce20774ed00e,0x7fe88d58aeab82f37257,0x4dbb3c55afde819d09ba,0x156ce8d9d96215243af5,0xb9b364eb58f47cd3cdd8,0xb2dbbc52646562a4ded],
[0x680aaadaeb9d31f8e663,0xfcda17ca1ca4aaae9885,0x2616f33aeccd4c376a30,0xe919e0d6dd8c1ad091f4,0x977d2289306417b16dd0,0x7e5efcebc37c9a505975,0xfa11599479182ad62318,0x381c2693471d873f58ba,0xb223c1864910aae4d757,0xf5162836d4388138b61f,0x70b8a13ee0cc75175037,0xdbf30e426139c67e791e,0xbd1b17a242d10db48526,0x5a8ec8f504e86cc478e9,0x49144a9bcbf76d1f922e,0x6e368dadcad653076e50,0x4961f15df02fee261323,0x9a28dba5da1325c912c4,0x3f6bc3758a4b11e7a3e8,0xf0b04c61d87536ce3c3a,0x58ab6c2276cd47731638,0x6be6e9f733496d81efb,0x81127e13217952659eca,0xe61460a83f539928e209],
[0x8fa7253ed9387a2d733a,0x601df903a410b2fe355a,0xf747238ff15883dc9585,0xb4f8e7870ae85c9cece,0x4d1a576d3bec05a82a87,0x8aefeb6e7d2887fc5310,0x7f270000dc6d7606242e,0xe08aa93e02ec82e9e732,0xc94ed412dc0b66212c73,0x6f2de83e01ff768a95d8,0xda57436c6ef1c267e387,0x4cf00a23e8f2da06658a,0x5a308815998833804e10,0x893dc5f8042b55aeee9d,0x9ada8001da03028d3d52,0x8254c1540d7096e72d4,0xb76cea95ab4c15080c56,0xc18bb2926347eedaac88,0x74c93766d3f751aa5e78,0xa700099914ecef2bafc2,0x60a4977c71bec1c88301,0x52492f651f59189b9e0a,0x9ca1f4ead64df6c2b1af,0x257757b0d215b7944785],
[0x201d75b209687ae05404,0xdc97d25ef4b204c1139a,0x3334839c552d623dcba6,0xc6a7c56b8208e4e0d85c,0xc47b55fdb801b2c7b3a9,0xc734d3c831c0d42f749d,0xa074c7dff05e5279efc7,0xe843de8cac31336596b,0x4dee0c695f9800f4ba,0x9eb436cb10c85b24d923,0x38e5d130a84f845792ef,0xbed95d0bb43210091308,0x56db2f6e6fcf3291c04b,0xabe25bb0c9c3e22b2a1a,0x309552f7e2b98038acb1,0x35b86adb8558130f6a65,0x2b104693fce7139bd222,0x2f0f46eaafd5c835bddb,0x9ffdc5dcd92c16ecc24d,0xa6f74a0c1e03d7388f,0x3a127e6f258f03306242,0x80e89e5e8f03dabd6a58,0x66c403c1eb2c028e8ede,0xa08a61cb097f28751ee0],
[0xc678832b2b11afdb4af4,0xa40891dd846a44a82137,0x85db980c599ce2c6a268,0x4c943045c316faa26d41,0x5eb46d71408d72de4852,0x6e860e887c5128c7b6cb,0xebb23c32d6dbeb69531d,0xf789897002c998d0b043,0x48735371c4942ece0b25,0x65e4b4cd79893766e556,0xb8c8028a1e90f73d4fc2,0x213fbc30b085500721f4,0xe0e6440ad9154aefe43a,0x5bf19f745bde7b61a6d8,0x876757a47369d7dadb21,0x299265ea08565cf2bad5,0xcbd3baaaedeecda653df,0xce01b633ad26c61ed8d9,0xf04c04e4f87502924bcb,0xa5b5c72cb8ac5b92fa09,0x92a37f75075d56b9e232,0x6f33bde8bcdcbae0b0e6,0x1b1400d12d013d1a81ac,0xf62449fe95d48618ea33],
[0x5f7609ba591546e4ee7d,0x8355a0975a23b6a0955e,0x687847f01fd6b23c3df5,0xb9f00a8586b7263baf07,0x5bed8854759411a73887,0x4d9b4a8904e81aa09510,0xca6437458c775a757361,0x6504ed4fdecbb839faeb,0xcbb4b732fc7e440fe2ec,0xc40cc1618a3cb36d9442,0x41aeb6ebb263aaee47ea,0x6b46b8ccbf269c707c57,0xb7d6316445264d3ef235,0x89f84ea7c9c992513a55,0x420e8361608f3e6e58a2,0xababf2924a9f25af2df8,0x828ca30db4e3bc55379c,0x78de5b055ffcab611328,0xa2d31cab5bbb1e6dcc81,0x6dcbe4e291ec7f2d9382,0x2ba62a66b99880fd0412,0xcd253d65444cbf3b322b,0x79aec983868a1c03ca51,0x89bb35ec5fe23c909197],
[0xdaef4a97c9135a1c1650,0x94df578d8d72e9628a1,0xab7794694bd5fb77a4fe,0xa62271c8b5aeebcdd6d5,0x47165138f3b5aab6d327,0xe007520b096a274b7f44,0x8f17153c9d17e5c4a3f2,0x130cfae7f2b2488480a4,0x50756bfe0daa1d6f6626,0xd8556ac59d98ffd54dca,0xae118cfab8e8b95df22,0x25b656516c4afc95acf8,0xfece0f53fbef669a68ec,0xe3b7deb453d68ad42164,0xe9349986b8287ffec9c9,0x90e66929e900b23c6a15,0x6c45fe04b5b9258f86a2,0xb9bd1f468f83c05323e7,0x8cc351b317db05a0d5da,0xf362b662608fb735ddf2,0x4608c067ba3a044f8f62,0x594d5dc6f348b4e407dc,0x703c7bc5def92ed23558,0xd6ee42dcbc2210a5fa7e]]

def tile14 : List (List Nat) :=
[[0x20690cf988547742e546,0x5ac568c37346bcf79dc1,0x6f8ebe1e352b1a55478d,0x49fc626ecaa2f42fbbfe,0x64cc6d14c1805c092617,0xf1bb907fc2876326704b,0x4feab8f00be48e6ce41,0x2effed2fbb4877c9f65c,0xcb47736f8418ce861eac,0xa8ad45aa410543bc7b93,0xd58b3bb79dae374043ca,0xdcf9c239f0c48e7c979d,0xfccb66f2e86aadd489b2,0x33207460b84a8e9f06e0,0x7d93aaf2195e93993f42,0xf1e2b101d1a4179b2e2f,0x70b7f7527241bc9830c8,0xba415a02c6877d6d8f95,0xacd6d3ef6f85a09b6f8f,0x3a744555b621b9c5a308,0xf972effcedef28106726,0xcaf83d83a8651293264d,0xfb197a6de0f8543c8537,0xe3c9849f0ba137a80654],
[0x9e09261ca563037b9440,0xfa686d2a16d7a8139641,0x1408222d1f2d9e1b6c0e,0x553f9dc2f05c74f9a52,0x5d4670c4f728e45ed072,0x72df72e0c06b65dcaea3,0x74243f1eccca2ab0d097,0xdc274777272e5b98e33c,0xafdd5d87405fa8942bb6,0x4ee71121dd736550c085,0xb8da740ce48bb14616,0xe7278ee8daac4f60b9cf,0xb01aa6444b0db1510cef,0x718e38375094577a6e3a,0x67054e1ad5aefa5d984c,0xb41d095b5b4a72c981f1,0xbfc666e37780400deba3,0x26f7d61b0d5a96c89317,0x7b75cf9161f1845e206e,0x88f7e64015c07b7296e3,0x36b997f0adf8fc8a7a7a,0xad41f170320869632106,0x3c25bda013c9e6c124ee,0xe82fc3f2daadd6ae7994],
[0x2554dcb94d5f9ba1b571,0x6863605bbfd93561a199,0xfe2da5541e2be7c7445f,0x9ee843f11e1a4dcb4940,0xf065467cf15b1ce8436d,0x365ae3ff5f164081cf74,0x11e87678652205ef61d5,0x97661c6b87e1fe6bd67a,0xc227d02518c93b1a4b2c,0xdcc49d5b81ddccbc346c,0xf240aa1928cb4d215b5c,0xa7e72aa65fdd62b90644,0x781c9aeb562d1a5e06cc,0xcfced4cb53d63dc48ddd,0x6097272fa3fbe2944c42,0x2da7229a894a872bafd4,0x5820f0bcd58e3f34d5f2,0x9fcf7a9a6a5f6f3d1941,0x352a29b3a671961314ef,0xe20f0bf1e4adf0d88fce,0x70d2907240984a7faff,0x7dadec310d92e89bf721,0xea104f784a6db734a372,0xe7339f56eac261a41d54],
[0xa190c225154631f03a27,0xd95a0e38b6360eaf74d2,0xb7cc3362560131d90019,0x12acc9297dd1bbe9e4bb,0x1f952fcb70feeb5984f7,0x34ca5b466a5d6ce765e2,0x2eb39bd8ce5ec98ab5dc,0xaf27967f0e6c57dfa7aa,0x67ca7da041f1ce1d0b81,0xb5ba89b845ad76b3eed3,0x9ce0c106256eea28f0fc,0x4c4b08389d5c18a443cd,0x466c87a4c203d44eb561,0x53d0b1e3760214e8b2a3,0xe8becf685b973f63798b,0x19dc6c5b1b0efe2caf22,0x3caee6aa794db4f8767,0xbe5d550254e11cabd7c6,0xbce092135e5f3a3a4538,0x53fec6b5436fd2f034a8,0x612e4b807bde7d4caa13,0x76bf5d8c6eccb1897d4d,0xcdf72185b96f2e39b3d8,0x10e0570672799d2ea2a7],
[0x50002b895fdc778ce034,0xd90282c27f004356cbe4,0x1167bcba76e0a581e73,0x7101722aa546ebf7174d,0xccecfeb374bd23ece975,0x33f6751b65cbbfb6a054,0xc2b984d6bcaf6be9d506,0xd2ba71d637c11734d57b,0x74fe518dcc82febead75,0xd054e4051feff66b9f31,0x65f76f0a00817a7b7e6e,0x6cfe200af8a0d1acbca4,0x3036bda0749b325439d5,0xc697229e8fdaea48eaa,0xd3471a8708c65fad06fb,0x858b007e76b4e2e91e89,0xf6cbc71e264cc5848ea2,0x7630ae273de18af4b454,0x2db082377df1813638ad,0xd3d533ce060212536a25,0xa75c87a5ac9364309d24,0xb8502cbac60c2a29048e,0xd7e54f7efdecdfd61a93,0xcfe72ae087a806611d9b],
[0x6243477756fadad1fbbf,0xbe508952ef4fd7812042,0x88f50d2c1caf125deb69,0xae4a541feabc6ae707fb,0x483dc1314bd1a31aa8a,0x81d6488396cf2e4df775,0x4aa1385ba22e92c687a1,0xedd8eeb571c2e749bafd,0x7ea6574ecbfaac9ac65a,0x39aa6275928d11eff96c,0xb0d43374f85bd4fb65f,0x88d892a6d12fd3ec22cc,0x4189b03f3fd101df254a,0x52830032aa275016e0bb,0xb4f29aa4e4d48ce0b94,0xe2a846c923fcc00651af,0x311c9f132531575221a2,0xb852e38bde890a875cbc,0x552cb17456b667575d67,0x9ff7f40888fa0e0bd117,0xd8b17d11d7ce59a0073b,0xe1c64d517a35a9675f6c,0xca839914edba2b762935,0x20ab4d85b55617c342c7],
[0x5d742414697ad3716746,0x88aa91fb03fc89364fc,0x4f20bf4f47c559b3e309,0x2b8b8db057d2a941b74e,0x9e403c2cf3356a9b0bf2,0xa9d8eb3a65b677a64009,0xc960fdbed835cd00dbd8,0x38ecf63134635c9207f6,0x8b9fa0146cd035471ee3,0x244c31c5cd18f7275851,0x2a8408c824ead002380f,0xa529bcb979ee2abfda94,0xce8bfa9ad397e7b4bcf6,0x14d7650ae16f5bda1a95,0xfc9dac512f3dcd1817b2,0x8a28101e12e0493e4980,0xd58c158948ca05a670d6,0x91edab4f1938ae0de836,0xa384855f91af95578124,0xa39b6a1016a10295823f,0x62b82e9faa88a3aca90f,0x2165f8e4b912fc061e9,0xf76afc6708c95bda4cda,0x3b9d8d66db2250994011],
[0x6d9a589305115dc2a7a7,0xdc3c6e1ce3ae35b15e2b,0x2e3da547ac672ad41a9e,0xa67eea1e439adf2132a0,0xce5281b2e4c9b8cadcde,0x6b32c87218a556bb95da,0x92dc69cdceee0409c5ce,0xa7b7284c0eb8746680b8,0x7fab74dd13a53e636b17,0x618f026ac8020c31a287,0x14bab49995df78433397,0x51baa6081f7b0fea3124,0x16466d085f030bf5d136,0xc7d826f2f6e3f4d5dd24,0x62984928114786f4da87,0xd2a131e90174a0ff1348,0x47c7c64d7a94cbaa06ad,0xb75f91c3452d96160796,0xab6e7a8f5a8f06cebe1e,0xf2a3411d633626ec7869,0x2d0c3faab3c966336559,0xd999eeac193602157805,0x425b40ca4170b0767111,0x9360cb60a29aa873ae39],
[0x18e1b82d6ac8b5f35a47,0xc20ad520883cd9f7ffb1,0xa2cf547007f0ac323963,0x34b61c884f964c9f2ef9,0xe5c1545a3d3f200315ef,0x1172bb5e46549d970c31,0xb4aa29850db61a5b4b80,0xb5667682e8acf3a9f7dc,0xdabbee6d11f50ac64c,0x85291ce8f2b575cb6f6b,0x8d58a195994977d8ba41,0x16a7ca999c41a5d5b596,0x1b9b31e91321753127ad,0xa8df7d223cd2aa98ef18,0xe412752a161fd647ea71,0xb605120decb48d4d39d,0x34d5b015d8173c7f9c2,0x9f0818d6a0be4bc8ef33,0xac5ba6e2278ef6f88e32,0x71d07ebd3fe8ed004d93,0x83c9351029de23fafc40,0x45560398fb3f8f84b416,0x7d365a5b48f68c921cdc,0x6a88eaa3163967aa6319],
[0xaed7129fe4a4b58ad48e,0x20e197763e7734aafaa3,0x4115253fd45a1561bc2,0xd7f24d05ebf3dfc467d9,0x5f9dbd836e51aaf818f2,0xa48f0995884e70f114d1,0x50163c3619ed4e6d52eb,0x57acf7e07080f4532a3c,0xfb52822be2b26f8c03fb,0x33076017a9349b2e0bf2,0xa2ff567668c0be73a58e,0x9f76df20219dcbc02536,0xef6ba0ec41aae3234aa1,0x7e5a9d30c598a667d424,0xdede997da1a46f325846,0x25351aaac152f628fdf4,0xd85a35d0ce76fe647ddf,0x94d616a1552f53ce06f1,0xab2af1b9e0baafd897a5,0x409f8d29a3a38bdf98d4,0x976f84bc4e31bdba153b,0xdc408184653c6dffa308,0x3126222536c48d3e410b,0xbe7326e2daa3e57922b],
[0xeedbc8b37fdcdea8ab49,0xe266358a603c214e7ae4,0x9f421016a5e2da7d83e2,0xa92b31b2d306a595d944,0x39561894200d49ee017c,0xdd4bbbe56c19a4482dac,0x8aa991cd6c089989cf56,0x7250336415e7848e64ac,0x5b45697510a633486a7e,0xfcb1fa2de764d07b89f0,0xe06fb0257f66646791de,0x9b88ca829f6c013447b5,0x831ea84394729fa51dd8,0x81b05be1ca3be7c4b81a,0xe877b70cfc4a818cdfe1,0x808eea5abbea5e8f6807,0x4685efedf15671b5a7a8,0x3a4f87a786074978d973,0xd812eb057ee282a6164f,0xf11d7c72429b43c1114a,0xdab229ac41cd5f21ebaf,0xc91cf608525b2d75be80,0xf7e6fd7600346cdb2343,0x77f811667057c502f420],
[0x9a8f671c533559e869ea,0x1df4ddebe4741e6f417b,0x5d025b8e00151be675e0,0xf2773b7b826c835c1d35,0xdfe02a0b615a40acb2aa,0x7ce263ab13acf822fa,0x547fc629c387399ce23f,0x19345a72d3a36c7242a2,0xc0d73f41b12f3b3ff6f9,0xc6efaf840aa6b231a07d,0x86b8c0f6a9c04a476d65,0x94d30df3439059d0b677,0x2be255db170ff42ee949,0xc6750a94974572bd51cf,0x9d4e5d484ef891e7c3e2,0x37f098098d0bb608c794,0xb257e120a6d44b636c39,0xa67431f6765807fa46e3,0xafc834e3747410897f6f,0xd2d2c090f87146068349,0x217f45a17effeda3534b,0x703be22e9e2f86b9039a,0xbf1578b4c848a0e7143b,0x7133748482622f2071aa],
[0x77d2295590d708fffb01,0x7efc2bc51e43c3b0810,0x8f5ebb0ddf886cc75098,0xadc1633557efbdd5a502,0x90d2759b25023cb3b46d,0x1613792f778156c88e0c,0x6484ef5fe110e4696eba,0x426b76d936a7d6b78f72,0x511861f053398a470cf4,0x1846bef3fda7bf6036f7,0x82b0e26525d4c8a5c78a,0x118af073a1417415c686,0x9a31613d2c3e328e80c1,0xd7ae71f88ee0fdf6fe3d,0xde8162a4b95ec9e10d95,0x8fe1ddb5154c0be9ba47,0xa505183167abe5db159,0x10a0134589e3e0351cb2,0xbae6d0a247ea181a4628,0x4260e0df1b941c78c1a1,0x3667153f028fd591bca9,0x17b737465f805b580da6,0x43edd9b1f60421ef64a8,0xf4408be21161b86a3fe9],
[0x1b39dfd7e71f86b1208b,0x7e9aed74a9a160be1994,0x3f0df2c41911cdcf6821,0x3db4772f239c348606a2,0x712d81cf019843d84b4d,0x60e433e2ceb46d4dbea5,0x31d8d7614fccdad2bb4b,0x13a50a94197c0025a778,0x521b6efe349377499a0f,0x5effb309530a8cc8384a,0x7e135e450c586bb5031d,0xfe8a3a2fd3e3747bde8,0x97b5a6ea81a47f52f834,0x4cd403bfe43201178ca6,0x4fcf2b774c6ec7446c92,0xe570c0a73db2e2595fbc,0x226ea223f098c958e966,0x26d2e02d59eaae38279b,0x36f33f078362b74ea9c6,0xcee0c2276d5c964b169d,0x21d75d0f3d2e2a8c75a2,0x66aa7e540409721f0618,0x450eab0ec0d9b2c07a3b,0x340a525f7e5aea22719a],
[0x902e0c7eef9681251d92,0xbded1615d4273e60c253,0xfaec1d6977c3ecce637,0x5e9d3bc4a711cfd1cccf,0x4c31f4ff63bf8dcebc8a,0x79cfbd8f120b8dbdc6ce,0xd0a0b49be7ab6ac88734,0xca080fb64c2df953ed0c,0xd73498a2016cc88c61dc,0xabf09ca58c26d4d4f614,0xf46d51793de163f731d3,0x6f28cc704b40c309f1fb,0x5f3e72d3c7681f5701dc,0xd24cdb9f31ab8037c2ca,0x9e63d967cc1254c0ed4,0x3ba7fdaa43b93ff3505b,0x4ce2d6b6eb7c6c1e7880,0xdad72e87507fcffcb7e,0x40e4fecb4b2482d72cb3,0x8f78513d31cfe128cdd5,0xd8a7c69ea049b558d58c,0xf2079b45c03345582a31,0xe7333d838e88cfe01cb2,0x8fd77deb192e97efc286],
[0x5ddd66c3de82c9668fdd,0x390e253c7a7e4ec9e792,0x36b7bedac9c74653719,0x4185bc0e2cf525823ea8,0xf296d306e4f6fd81f94f,0x5c89bad42a9f22a10a33,0xe61f3dc790fe78224064,0x2b2e84a45619523b261a,0x77916216e76fd5094b4,0x840074a9be740f90c28c,0x59445537d0b6507f1439,0x2dda26e37c31d30711e,0x993769da4cfd50fc59b7,0x27b93c0191461dcff760,0x36b82c1485c4fbc8edc6,0x92217da91126867b4774,0x4d11c165691d273f2e47,0x6eab63cf4ee161785260,0x51c2ce4c82ec9d267bfc,0xc8c09636a3fc9f1dc4ce,0xe181ec838cb3328d6111,0xe7760b8cf40daea1a1b,0x3549426bff970ab4e6f8,0x93bea7c24baf330ac2bb]]

def tile15 : List (List Nat) :=
[[0xbfd7dcc4c4311f9fa04e,0x921412cb2e4f0fd4db32,0x715b3033649f6b0cb0b0,0x8678a08095376e4c1a9c,0xbf30198f83cc06e0e380,0x8db9a478fcec5767b51d,0xbeab7696865df42cd034,0xb89bc9fc7a49db2c15b5,0x9e5e0eab7e38b28c6653,0x98524d1153ec9bfc5f24,0x77fda9e3fcb155cd02dc,0xf3120473283184366b41,0x63dcf8040ab858fc33fb,0xe566ba3407b190b8fd97,0x7df70c4fbe047f9e5156,0xd909e1b023159a34b056,0x8dbc5b951d12b680e0ae,0x231e27bad56f2e7cb035,0xf8f7b0032b86d7b3993e,0xd323dae20820226eb865,0x2d9f76ceb3c1d763a73d,0xcd371d7af16ba1fc2f6d,0xce260e611ccd80e596fc,0x9ea886115fe4a8060255],
[0x44bcf184fe54b792e80c,0x6ab32324ad2219b0ed32,0x3cf0b1ed2c9eab7e1f2e,0xf6170925b3f07049557b,0xeaa749c2df27aba5e70b,0x4eff5e8706cda4a28a0d,0x5fc6869d9b6d81c047be,0xd242eee7c3916412af2e,0x4dc8362bf5dc6d90c933,0xfef5d54b79f931396496,0xfe7512b90c4799dc8f0c,0xae19a8961ca8718a394d,0x3fba3fdb0a450048358f,0xe136f1c054e26c488aae,0xf415d81b1007a7768ed4,0x5ce9a582eb3eaae0e945,0x6e6b90c9d7a9ffd062d2,0xa6d88f09066edc9edd7f,0xb96a7489e536e0cae012,0x90f34e134cbead8245be,0x60cb1afbd60edfe3cf5f,0xdaf6f7e74dec884fac58,0x64312c9fdcc5993a53,0x773b289ea64d442fe9ef],
[0xf1fd1fe23ac63113254b,0xbe8a400b0c61758f7991,0xad7b82c5acb74f3fa0e1,0xbfe325d3e8a0eb1f99a9,0x24955bca6346240528df,0x87d685199c78730452ee,0x9597abef641dece4b667,0x9940c33699558f03d1e8,0xa22116df3554cff7883,0xca7903a7e030bff02177,0x6e8b0ab6d4f349ab8c56,0x955ecb2346b4054919fd,0x9a3025edec88ef0c4a69,0x4fa3d6af87ff0f938048,0xca47bc041fa5c4ff8298,0xcaba62bd12c0a867c8dc,0x4fbc8eb271c47d409485,0x419f84d47343c987116a,0xd54ec81147b665c10650,0xb2c43494533a377c7f6e,0x76cf2daf0ee6ccb51672,0x6e55817ee291f0f53003,0xa234bb4b06679437c65c,0x1e0ad406efdb8b5899af],
[0xc6775585ad567b323036,0x724a76be6d9e56ab5af0,0x75261181a16101b68d0c,0x50030eeecb45b084b4c,0x4ddb4256995ec5db567c,0x48a08c23a86b72a54815,0x64990ac839be0e8653be,0xc1415d62cba395a22ca5,0x41b280aeb2c5a34714b5,0xaea99fb3d8e0a768336b,0x69d203ae738bd509a754,0x4d326d93661e8e1ae56c,0xc65f1af263b208c40551,0xbb68bc9750c5219843c7,0x260e7b2a27fdac10d3f2,0xa8a3ca6da004dec7c68d,0xaf179fc94cb9645f7727,0xed87a555919fa3c97aac,0xcdb53db42cd3c870b18b,0xd15daf5200095414d26e,0xb614741b488540ca7de3,0x325872edfabd93c41091,0xc5a1ad20fc851d885d08,0x5d5f28e2ea9d9dc699b3],
[0x72db4a3d2e785156d21e,0xd3b7147587053fdcc070,0x20e5252ffe486be25854,0x9ef8b2902d5052431162,0xa71edf98b2cfb90f3a97,0xfe986ff9e9bb460cbb5a,0xd891c5fc563913a23c94,0xdd40a4f76592c44980cc,0x3e9f3201a94164f74157,0x5bc1c9ca4c7c09e54726,0xb425ef1d100f891344ce,0xd3e20cf643b729ee42cb,0xcd3b029f57712c748287,0x488eb55a0f422ea30079,0xda4db644af1f77df9068,0x2c9df610ea993f3c4c36,0x48f443c3de192e9e41b,0xc32bdb0f94af82fb1bdb,0x9de64900ca2383bbf327,0x9009013f6d36e43107a,0x9b6d9728e32c107101e0,0x4280539dbec4d539fbeb,0x3c7ca2990ccc883aa4be,0xcb177207a7c5b20b4ef2],
[0xcc0a785391431db68fd2,0xf57dff1e71645c8d7151,0xb1af94825c2c55cc7c7c,0xb24f661cff72574dfd5f,0xb070bbec2092efed92d7,0xaf494878633aeeee2132,0x9c03683fd62331771237,0x684461bfbb420d7b9a74,0x94db11f7c79788d9e49e,0x927573b1a97010370a11,0x4b204d16efceff704e81,0xfdb1d7a47e21158ec879,0x466fb5195709abad34e7,0xe715d022ed8a92c572d0,0x852075bbcd201ef94abe,0xf1eb1519be5da6fd2e55,0x40e01ab4f29c770a6aed,0x6672b95a47f83c1ad2e2,0x78db1ebc5f4db4e0968f,0x5173f5116dd542dc4727,0xc0166d5669f44bdb9cc7,0x24bdc3d2fba505280095,0x6206832f85fd39762639,0xefb7aace3820d084f9ba],
[0xa9ca57d30f0fa90abaf8,0x1b0829cdb531853c359e,0xd591f0f832a1afa5b41e,0x783b6b5f9ff401826771,0x350bf915706e2c5cd517,0x4b33a6613ccbf4967427,0x231050c10d838accec7a,0xb219e3c9b0836e1bf56c,0x6a4c422d53822af91b31,0x51e2e7b6e9c38a2b1a74,0x844782395396218609ca,0x5a2d1de3acf28abc2e50,0xbb2b0179be550941fbbd,0xff4ab630a2d9cab57e43,0x19720312db0711c7b1ee,0x75fe6f0696d7b698757f,0x33d6bc427c4ce9efa9e6,0xea6703d18c5d9bc7c3f,0xac68c39cb8953adf7972,0xdc2941f9a1c598c01f79,0x4181111089fe81a5dc78,0x39a3d9ad33fe7b0fc278,0x5561428576f50970afb7,0xa6a24d302fd2815ceaef],
[0xe50fa5eb0c3b38bd4f60,0x31a9d29ec16b89283f7b,0xad8a59825b8c5cc6c09c,0x358f734f621c634ca955,0xe430282c74d057565b01,0x3b0dbd422989684c6e04,0x90b4c9a314c89c3f6097,0xc26d15f1fb9eab9225f6,0xf6b6f1e69746b8cf2151,0xab0ec7a2fba6bb585a50,0xae0a2b0ca1443ba53193,0x1fe46ba5639f6cafa58b,0x1dd9e5360cc36fbfe9f3,0x395208640d908f70a585,0xc2746435d0ae903268f1,0x7f0e35eacd6c7b9c1c36,0xf9acefef12de5ea03a14,0x862bb3632871ada10cef,0x90fdcad205b255dea33c,0xab9bb3b070d03fd5379e,0xd2d6a27f6c6ae12a325b,0x656ec46a77f834e61b46,0x24cbbafd2d7382611068,0xbd9fe6b3894b9214656],
[0x1ff4274278cfc8ff940,0x325b87341c51c924fb03,0xb0dd9b22e6120a4fb228,0x46983a683bfa227912e7,0xc88c52f1cb5465bce8e6,0x7ebea5a19a48bf4c19ad,0x930ba4d46a2659ccbdb3,0x7327d1a782c89d0181c3,0xbe76d309f7a392a28730,0x46b798cd48c266ab0212,0xacb3df9780223c67e939,0xcf472fc7ec57cebf3fb0,0x5d1f7b88f672aae41bfe,0x2fe7bee0dc7cefb11421,0xaa17c817af3304fe4c6b,0xf54cd6917870eb6b762b,0x4c2c48d1ebdf7248390c,0x21cca8d73cf5cf5683db,0x6366f53f7e10df9c1d86,0x7d7e10de3ebb453e8089,0xfcefd1aa55f2ca96a693,0x87dc4bc8454bd2e29b07,0xc0248435ac2ffd4b1527,0xa9f3bac5a7eacb5ffd28],
[0x8ee06bbe9edffaaaacf4,0xbffee2cf88ceb3555068,0x69facc6c0ec91d726f4f,0x7aa5ac87a972708779ae,0xaaa0358a9e5675235fb0,0x87fa0bcf433484b1e8df,0xc19efbf9a8e500a117c5,0x8f13932659e6a2b6b788,0x927e8d85c579281ce778,0x7c5d6515700b411c3410,0x6df285e85977df31e05c,0x7c8d3fa68a95cd75a44a,0x84b859a06e4a27b78915,0xa58932c15ab0f25b49cb,0xfb0ebd06c9377a3c671,0x6b65d72e24a123ca1c09,0xd97ee4fb96a225cc6d79,0xbbd1699da09e10c282bb,0x745f5afe115bdf0806f9,0x5a7cdb618d8e0f691b8b,0x7d80021799c05968ccc1,0x7b81b6684cf565aae82c,0x8be388b79a7c60ef3850,0x7020097c09d99f7d7bda],
[0xa3cb8fdf2ee5d9f53de7,0x90e18b894482a2460095,0x28602539c36f98b3bcc3,0x3855c3707ed06ea466bd,0xb5fb614f9f545660c73a,0x8eeaed53d2cc2b219f93,0xe6dfde68b1a77ca3454c,0x1294eb835d8fbe4ee590,0x8c3737fd6eff28c23310,0x5c88baf00934d21030db,0x11bbfff725fe559808cc,0x6631f66a733ae1b4f920,0xb4cf3f0863df592867d9,0x56689723958741c8f801,0xb4eb01de85697ae4fd41,0xf8a5cf10eb190c3d7b5f,0x515d55fa81be450cfb7e,0xcd5ee28ebee3edb1cd54,0xaf4cf7b02438a78d379d,0x6fa0543b2886dc767fc6,0x28c396b0c1a3d9200a89,0x1ae3996718f70a73958e,0xe3f2aed8fd4e070fc1fd,0xd10fb356ce7174bc06f8],
[0x5af09ec477c010685981,0x41a87a0788b7ec2cb10e,0x7306b7393c474d0161c8,0x6dc06d78a3f55b19b643,0x243ac074ebf7187bfd9e,0x6c5d6839711adab9b12b,0xe1cf8bff1c16bd29277c,0xcd0edae6f20323e85aa,0x1cb5b2ca97cf4022889f,0x955167df44934874aa85,0x35b06118f1b5425844e7,0xd37cb8497d549613b51c,0x9ee92fbba2fd5044d8a9,0x70870992b2c360b7f40e,0x14dddd94b2a20b8acc71,0xc56b7023739ee54d09a1,0xc9d5dd61cf3d39525aaa,0xc9208b0bbb1e24b27104,0x813f8ee00915f6be9649,0xae1c27c9e4e39cd2311e,0x43744f44ffd37f8696c7,0x9ae89c0daf94a2bb2b01,0x22baaf216ea11a87c994,0x7af3b9ba320c1b33da50],
[0xc509207cda3154e159b7,0x6160f8a677b83be83c62,0x2b1394d3a2b56739e9f4,0x8406b57fe85561623e86,0xaad8aa41756e097a3776,0xdb4dbbbbc527c8d96716,0x11d380ea52eed3ae278a,0x912870ddc8eccda931ae,0x9bbc1739c1620e9172ff,0x3cd72bb78601d929a2f4,0xe7a4c976226d16b5970f,0xfb7c5bcfe33f392105c2,0xb1f4c404f20bcdc6f3d4,0x8dd99f5ce6a1f42c7f48,0x80d254e557d24da2beca,0x6545fbf4259984a31b34,0x7a2e7296c98dd1d5e01a,0x653bd8a55478890ee906,0x6c956226a1686e9a798b,0xcfd2d165f642541f4b3f,0x63dc3a92d2cd26e832bc,0xf75e120b8087b9a26902,0x1ff385e552df7a5e7b11,0x6be9c893c3f324cb448f],
[0xdad864a34922052d6e95,0xcdd2efcb3b0f663b2595,0xbc83e9ceb9602cc53dca,0x741a4df97bf7103c89b9,0x4573dc8ccc98a6b8ed18,0xa000cb31cd98a8fc0d44,0x99971f21fa083af5c416,0xdaf515ea05f6bc9ac7fa,0xaa660b5618d2b75bfc49,0x92aaaa64bae10d54ee95,0x55b0fa141b2c7bd0e133,0xefc6a58119595b0a131,0x9054938c27709557a79d,0x5701bdf7963d85103d61,0x31e82f67701560c3a8a5,0xd0ff3e96a71bd9f9636e,0x9d7c64770e176ee3656,0xff04e580a47e60ee221e,0x9c5e5c51195b2b41bc3f,0x19b8d9ee36bd1b9664da,0x28b082bbaa0b06306e64,0x959cfd635e5a21000f02,0x1b71fc7f33a3cd8165d2,0xe04b7bc037d3e8e9b8d0],
[0xa87f57ee6e00f41cc8a,0xbd6b5cba8d2b75a15f0,0x8378b98ff113fb271029,0xf46439ac5a9375e9deb7,0x7ff9611e8afc80e4880,0x8657e3272adb22a31a48,0xbee1377bb62936323a97,0x28484d19593d05ce8448,0xb4b0e5cedfb94cfa5a46,0x58d6b8e2908adf7198e6,0x1b803e23378e5bd83519,0xebffe0b9226690f8673b,0x4ee9724e17a520553c4e,0x74afbea184fade46c527,0xfb795822603fab473249,0xe1f2d3e4cd8c8d417d0f,0x1ac12917b8d175527d16,0xc850244ed72b8ae8984d,0xaf1caacef393372161ae,0x2547af3ff0bf0962e3fc,0x8ada2286b43462a1e265,0x856ad5edb741bb314352,0x36047fba7a6ffd7a8d83,0xc811ee9a028122f283fc],
[0xbdd8d2400d43883839e4,0xc2a45b93ce08513ebabf,0x398ca469f749cc1c92fc,0xc86ba9aaf9dcf42808b2,0x2396e14f04c195501c77,0x3dc7e27494e2edd25e1e,0x5f5485b080eb619b3531,0x6543d8b290c587a3518f,0xce7749c8e59f3a74dce7,0xd8bea86aae3caf7e19d7,0x5ffb10369bbf59a38328,0x8f9d795908544ae80f5,0xcd1188281ec6d96588e8,0xb7d98a16685ed5a6e10,0x8d8616a38d97b92dc8af,0xedb20785a0e79936cb3c,0xc8a3fbce485325ab7b2b,0xc92843d5f8758bd25388,0x970ccb672cd41bd767df,0xe8eee0756c3e63bf4032,0xc064f7543018a4245436,0xed5d8b241376f2ce27f4,0xf768d842fac9795660a8,0x5fd0d3a34b9d5f659057]]

def tile16 : List (List Nat) :=
[[0x15435b587f7f1fe4f6d9,0xb2cf874248774cafce50,0x9d140e3863b24d3aad08,0xbbf744a05f879c286b46,0x2560767a421ace531343,0x7e1f561b3b05963999aa,0x5829855d0e1339509689,0xcfd35a8b954ebbaafca5,0xe064053e4967cf0e1309,0xf6b7b0cd11250c4bd534,0x152c6a8efabe3099d39d,0xe4ac743657879c293fc8,0x22932e0476815d2b2708,0xd11f4192e36beda911e1,0x902ddfcad7fa374d387d,0xa94d9155d5d31a4eabe6,0x6db640547ad92dab073e,0x853f951c6cffefde0555,0xad01b200a55f27499ee3,0x66cd4c0dc6b200b5c70b,0xb94ac330c22a6bee024d,0xe1334ce3f4565dbf3e11,0x15cda9987300f4622847,0x8eaab3c5c796c84e3f59],
[0x3003b036eda7c2237578,0xb457fdfd763bf5aa97a4,0xbe68ec09099fb7d049a0,0x49acf9db44cae6a71c5f,0x4d9af9202434776ca2e9,0xd2c05d64f92e43422465,0xfc508424cb559e856f95,0x54d4475af939e6f5097e,0x18849b72d46132e2fa71,0x3e1542f931c154ad609a,0xf55512596e9ca2c332a3,0x3809b12fb6b917c19407,0x46a1f18cc9e7a210b6b4,0xa93610aff2a12a503f44,0xc751358477f98da2dfc,0x93b54e2750072b5476f,0x5eff55c6af9d33a4372e,0xe16bf0b9c0e7f764b03f,0xe3319a8a590b03adebb9,0xb7533f9861fecbc514aa,0xf80b3c2bd71df6a9ceb5,0x6325b5d7157b1cf42528,0x425535a496e334ab6d29,0xba511792c7bf00ec2f50],
[0x63b91329f3c3ea05379,0x9c0cf145923114ef3753,0xe81a65055ddfa303aeef,0x45b754c25908885b898b,0xa22d32bb6d234cadd5d5,0xc6bfc2e53bc90abe2daf,0xad04f61efcf1808e181a,0xc4505784915351ddfc12,0xa19b2f8f12bcb21fb416,0xc219748b8a60ddd8de59,0xaa9ae13fbb31d59aea7c,0xde04ae9f14e78e9562ed,0xd697bd9efc8d18f5d4f1,0x114819156c825c36c0e,0x50bcec9b7d0f2e1edbb,0x8d8e0bab818f5b499b57,0x8ef6b3166971acb222b5,0x97d36d0464891ccc2964,0xf1bf72ab60d5c8fba2d3,0xabc6c7eff1c00c53c4bf,0x8280250a63d2bb0477a,0x1d04a12f5e79dd8cda0b,0xb437e5e4d0f1ce30b399,0xc794b99a6909e0a30e78],
[0x1539d7d1cf71542de07b,0xb632dd6c2406144ef5d,0xf5f524605ad1efcd8236,0x603917dcf74054c39116,0x80bc10c94402315c8a80,0x54415cb892837d5e1109,0xd153330d727bc8d0df00,0xcc94c61f1a06a4a582a8,0xbcdcde8bfe47c0847e52,0xba51a404063c4e46720d,0x627b778b3e9c4a53f843,0x73076d240ec98b020084,0xaea53eb6e703e7d9f94b,0x78a3742e8320ab9b8e24,0x537a94de64d3ac8c8e87,0xa0eaee16671af46b10ee,0x800ead082f90b89b5c8a,0x3eb144e0c2dd0b3e2461,0xb1e8537ea1edf8b225f4,0x38871193a95ebf72e957,0x53c0f15ec9966fe5ea5,0x436b449e08cddf0cd51d,0xab402a46f148f20bdcb2,0xc0d65ff1657d67b10877],
[0xae958b89f03ecc33ec9d,0xac560264ee2eb16c47c2,0xef5feedc696988d9234d,0xf1fd78334770f7e59c1f,0xad309f03c184fd3821c,0x6fe05425756ac1e59b93,0xc63e220c488524582dbe,0x3c3ea187c278d3e6e21b,0x4500fe5403e4a7886e03,0x20b59e59c3d787d9e4bd,0xe3504a5e047708ba2260,0xba3be17d15641b588f72,0xe2b7ebac70283e43ba38,0xdbc6709dc493622eaad3,0xb76b189633dbc72abfb7,0xead4843bf8fb1ac002c5,0x9335d48f0cc2a303a08b,0xb6e3b52f8bde108f824,0x9fc6ad7de65bb6a85b70,0xd6cb9a3c2e7c5352932a,0x335e212a8632a40d86f5,0xe384bb29b06ecca82794,0xf55132bfb487f2acae76,0x47d618a0aee398a3af61],
[0x3e322b9e09d301bc6f51,0x3662309734a3f9743bec,0x1445102ebc473f6c0849,0xd8a13e97b1fef1b5889d,0x2c05b3802687d01dcb08,0xccaa31e9a1043edb215a,0xffa7a0df02b0cd23a635,0x4045f23aea63d6144504,0x6e8555aacd2bca0cd11a,0xd0a31f6597ceea440cfc,0x4a8096ddfd34664da945,0x84cfffdb71c49bd33eb2,0x5cd00f64cab9be06be2b,0x32696c135eb68f3fcb8a,0x42f52e2df6d8286c6b7d,0xebd1b0aec768e0cbf7fa,0x7e0ffca81eb3ea0d1db,0x35cf4ede3e58bf3f209d,0xbf4d6295a84d14e30ad0,0xd823ab85a380f3a0586e,0x4ccb8363aff80ec5fd56,0xde68d75f3d590e0b1d96,0x381c8dc9fffef8de970e,0xc9da74c41c0b3865a878],
[0xdee77377b8991c6cd9fc,0x4a9ed9e524564e1a7007,0xbc2df545e142e4575d06,0x53600d9e6a047fc725e8,0xfdcd713fbd897260aaab,0x31a15146012fad0e4597,0xe331a8319eedfe1d937f,0xbb6d22ac1f6c0a004a45,0x59b7ba53f5c55755806a,0x211e909eed214c982b14,0x9cc05515fb103b9e83f1,0xd6687a3626bf8b4d6cf3,0x1ec97ce86054ba77db19,0xa7a247cff5c9e31571e2,0xd5f3915c7af711f5102a,0x1df702443cb95d9b46d8,0x6fc5c3eb54ec36df5a2d,0x23e4073ffab6e2abd471,0xc0f5a455374f85074b4a,0xc2debcb8d382890b8778,0x2601e9bf7352849fe3d9,0x5efc5228922f6a4631c3,0x27c12fb8cc3bfa20dff9,0xadb912055553c6b4c1e1],
[0x689b8c4e5340e87c5c1f,0xaf2d9f607b3f032a2e36,0x9ae64e8dd9494f359192,0x6f1a936f1bc99ba2fcca,0x616b3bdf4a887307ddd1,0xdaa981d82082f7cff991,0xe3e06e849ede60ff8404,0x4d136b1adb6fcfe51131,0xbcfe8ca7e3408f6636eb,0x6a1a058ace4e6ed5c07,0x81a24acff472bf197f6c,0x1e880cc1f593b7e8fddd,0x6b834db679664f7fdd60,0xdba80475ed70cd08c932,0x9ef91f968f9a912d16da,0x998e5bad30afbb84be7f,0x862b38d41d09909a56ef,0xadd39f64b9874fe3474b,0x11ba03011c65b39e2763,0x71d020f27207726dabf0,0xd09946c051103814b7d4,0x49f02d09dd2215c9f2c3,0xf18979809e3197db9ddc,0x5dd6768876ae3235b35d],
[0x5efaf27b141d29ff716b,0x7d359814c5c48d9c82c9,0x44c81356870d550d01ef,0x92c7476fa06f76420188,0xf0896a7ed05019bdda6e,0x18a4d74de8fe79382db5,0x30c63c1ce2a5ecac70cb,0xf3a6d60eafcbd1b02851,0xedc436b2b9b23592472b,0xfc8a45644d28fc1843b4,0x8e52dd576a80501b899b,0xee426406ebe0cdc79f99,0x16935326deee61cc1902,0x42a5aaa0afa49c0ca70,0xbc05f71baded1638343f,0x4ec8d1fd56d0b117dbf7,0x5d8c8547950aba3aaa43,0x79eab185ac409f320e7f,0x2446b5af875f79692a89,0x76d036ee2763782d6cc5,0xf888b4fd2e606747104d,0x3169466847b35e0231d6,0x5616b46192800058d13f,0x9750da022e965f638662],
[0xf119b9e7eb357d310883,0x2251441cc7654f8531c5,0xad6799b5a5f46d79570e,0x1110047ac13bc8bf7065,0xceded07fdf9a6be744e5,0xbefea9b57d06a6be55af,0x3876ff516e6b31ad7d6,0x180827ab077e16609da2,0x4a59215360ded7e6cb10,0x2b681ed663516b9c63f4,0x5e4c0a93571c0e2f7603,0xbf95ffde66501459859a,0xdb1467ad94ededb1501d,0xb5fe40355f47aca52577,0x2c98c2ee0120479dd4dc,0xa910c38780a219806ae8,0x7785b2ff9e12e8733620,0x43f595d55dd86dcd386e,0xf95007e81f95d1f55e,0x94a70a7fb1b5bb452867,0x5f37f03846377e89a738,0xda07b17e36512fad5888,0xf87f0be18567549eecc2,0x1a5f2d81afd4938c5c84],
[0xb07733c7b3049f37345e,0x55108fde77b44acdf02e,0x7f5e2cc56551eaf47a26,0x7b4339e963024b961664,0xf96ac21f587de3b3dbc3,0x463dc3baae1a6521abe1,0x232f0d27335d1a40f823,0x85f3b6da85892a3a0d66,0xfe91ae9075aeaf55bcef,0xefe91b629c2d91a7bc1b,0xe3ad2d6393ce38d00a47,0xa4d962b89d55d4f86006,0xd6233cc1788a987b26e9,0xc619a39107bb2b47ac17,0x9d30af935cb9a646b649,0xc46bc37b2ecb12621f42,0xaa6db721ab92a5eda94d,0x9a5eea49341b9cd22eb4,0xdaf324f3573eb7b5c4b8,0xeb09b11437ceeb89d6de,0x44529a5a9ebb0decf621,0xd6f4860b7db5500dbf23,0x4f3a33c48cac27236f9e,0x82a92f94f90da6167f5],
[0x50c187e53c3b47a96b7d,0xc7aeb86f40774ef41dc2,0xc5124aa9f74cf2832f24,0xbdc1704f56e75580f8f6,0x154aae703b363dd237c5,0x471dec41b8ec485786b5,0x350cde175b24bea00408,0xbde49d0d97798b2f176c,0xab481c92566c1395a37f,0x674876cf19b812499a36,0x595904e11f4a0c8b68ea,0x2436e4f0230aa7012ace,0x5d8c959100afb5071146,0xda20d34a6f8f15eaa14f,0x465be5d1d47ec9645e05,0x16b3c52576b7db8ebe43,0x454b065a971eb28f4a2d,0x2e5756daa616991f11f2,0xdfdb3e36a1244d595a80,0x8ad88c871c9551bc1ba5,0x965bd0167d4dae1c6c85,0xdee7abca1d96767841df,0xce0a139c08626d26507a,0xe7f2d05e799bcfc91a59],
[0x488cf6008039cc448f2c,0x1aaeaad2bf3091ccfafa,0x6574163dcbc6a5ff4aec,0x6b7e5a24269b6e0cd502,0x2be6e272adb3bb289926,0x642d51c9a6fd134313b8,0x2d2e00c6ef4b60b23eb0,0x8051cdee2719600b3972,0x125bf0201e38bd810b6a,0x656f04830b40de4826a,0xd08333786ba2709be614,0xbdc6802b387a73552698,0x817b70b49b7b7703d11a,0xe3603b6853481ff12857,0x190443bf7572c18335aa,0x6ae51b01318e28a741b2,0x1308be3343dc08e4f0be,0x1f87beaa517058a2d70f,0x2277490403bee549674d,0xc6084210976863bd8f66,0x7d8208bcc0fd5122bb40,0x74e5cce9ee72314f2acb,0xd78565db008a1aebb875,0x87c321967c6d0fa44dd5],
[0xddd5e19c01242c835a0e,0x61bc5d3d781fa86b47ae,0xf31ef6e0a242d876587,0xa9447cdb595818c2566b,0x304bf5933845d5c961ba,0xce86c84d948a8ae4c3d9,0x1272a059575784178ae3,0xa21a026e099d16d88890,0xe853dbb053216dd9095c,0xdc4f2d3adef96f966a79,0x1061a432bb1bdc3d4fd2,0xcdca512b4f02d4d5b161,0x3ae8de4c302f90a96235,0x75e999bc8af3333604b7,0xe3cef8723db5d7da9d05,0xfac0b2174e575c191f04,0xd7c7a5d6cb518ec28d54,0x5ade8d3542a64b3a2f27,0x7663d977b074d9d48f70,0x7e9bbe2b1d521574811f,0xffd6a57a98f1f523b446,0xb40ede93e16306a07b4e,0x89ae102a6742ffb739de,0xb059ad4b6efd8463331],
[0x6fac938becf119881dbc,0x1f80229c8321a0d4f114,0xe6cd47edfb326999aa6,0x521e48f3ec2137360fdf,0xd17fab86f7083a6eeb83,0xded26d339aaf93803175,0x70ab750e82fc333ec3e4,0x39d59a96af49fe9dbbd,0x9db73df800435dd85a39,0xe5565b3bc20ba665aa3e,0xdf5bdb85d552a9667407,0x954c8a9df30e395d2a4,0x4410decae6177e261893,0x48e1c9c13f5a1afe996b,0xb7e56eb92de17bf8ea11,0x317968ffba13508b9380,0xa37d9f512cbc27a468f2,0x3c37e0d5f8b075a7c336,0xf1a9c211d2f557e7dbdc,0x20c82e7cf880529f0e3a,0x7d6937a3bce0f4d43905,0x46916b4db629c77a3313,0xc20f43d7eedbd5e2fdd5,0xef74598a2b58cdef761b],
[0x9b43570ddc78dd9da999,0x92c6e570a5a9ab50283e,0x5137d8532c156482d579,0xb8e290cc7949e0b318f2,0x9ad1ffc1119137236894,0x224188c0a3f5edc42e7c,0x2f35d8e05b53c1c7bef0,0x47f6d4ffe492fad80133,0xe2fff0d3609e76e4da72,0x827ecc1ac6b4ed6b2078,0x9c9f796f04a86d17ba42,0x4bef4953102366b95667,0xb9157e96c1c86ea8c30f,0x3679d2b859e2fc72db6d,0x5ffb759a1c4c3e949a16,0xdea5b5a87356ecd3b724,0xf2ada052174542585377,0xef49a37e1245d92abf45,0x8e6163d7d407634f4dab,0xcfd5dc0d01bc6f451a10,0x844b80880c5754b7789e,0x76c31233b6f7ad820560,0x6083ef6fed64545880e5,0x2ebc0df32567125d8fea]]

def tile17 : List (List Nat) :=
[[0xfacc3766c81d6ce5bbe2,0xc4bb4109af265305132d,0xa761951f8e09b5580a34,0x77a932e9ae6f4a0051fc,0x382d873e6cf13584243b,0x3b8a0f326702079d878,0x11334e1b316ac6985f2d,0x6a048696b64d047a9bd8,0x3dddaee56974127a212d,0x62b248c843402ebe1fbd,0x2374337fdbe118018419,0x669ce8b10a3dd745fa04,0x87e70bb7249f955da27c,0x8fcbce74e1ab06f00cf9,0xd9e7234c6c0ddd65de7b,0x57d7e4cad3eb034b9919,0x9dc44b6f38c54a055c35,0x618b162a5daa169e3544,0xba2a5b67c08c2b2bc15e,0xcf66f93220ab5e79a418,0x9ec1f16e935597737c04,0x2d67cae566c274b02e3a,0x63f4137bfb68ce843ffa,0x9ac65c5fda08432bb4c4],
[0x40c0f5a96a84fdf0ebce,0x1c016a0158a294dc3e51,0xd1c9e3ee00c812098ce6,0x5bf6c553ef5e2215a582,0x2e06b6ce3fb77a3b55a4,0xb364a07edb3b83474a61,0x442d0a28fb198851621d,0xf51e31eb3ca0b5d72757,0xcee35d4b57a9a1dc8169,0x8223a3322142ae5969f1,0xe458b7bc478f8d335ac6,0xa0d30b6788d627b8dfd,0x5cdbaa1888f7de2b9b15,0xcbb65a8546a0c4d6b562,0x937391cb25e8871b7d9,0x37757b75ce1ea5f7cf8c,0x65e1c89eda927edc88b8,0x3e42ccc10b028017b280,0x6b6475c664584dfb00f0,0x40c5da895bd2753a79cb,0x607efd7b069cbc2e80db,0x602ee5d9b8a742a9179d,0xe1a750b08df52735eff4,0xdb89fc15259262d6ebdd],
[0x3df31a02561ecfe111bf,0x1389ba05e2d50574f217,0x3be017b8a288741710ed,0xde88957ffa0f6a03fecb,0xdf46198483149abc0fd5,0xf52e35081f8d67307b3,0xb709cbbdab66c1b9f401,0x363e92008e3abf0f43ab,0x7d879bcc7ec865d41fac,0x46635b7a910afec57d9,0xe8f3d4576e79a33839c9,0x7b0350fc14fa966fcea3,0x21f2d5e869a4dcda8075,0xb041d5ba64716db4fc4c,0x6f08659ae28e1ffe8660,0xba2e6d3e0123c9fd885d,0x18803bea40b0dccdce3f,0xd783280a353d49809df1,0x2bcaf4113d509ea97df1,0xfc150f5af273f7d910a6,0x7160d390696b80f0bc9b,0xa0e1e8f452e0f4034e83,0xf7a471f1cb3d710e191f,0xa1c45fa4807752732850],
[0x64994996be99088fc272,0x1a9b06980f73f3379fa,0x669a5d725ff2f6aca5d2,0x3270f18702babd9b3a95,0x7eb29e8ca746e00fbfb1,0x285033e894a649658bef,0xa027ef1cb9be7f0d1d9a,0xccc317cc8bdeeb3627d8,0x1ef40673b056f53d78ce,0x172bc8b8ce7e47841b90,0x8c00415f2861eb01733c,0x59ea8264a8a492db37d9,0xd63615431532da2fe193,0x3eb445c94685d5b45437,0x5f264b4cd76154e174c4,0xa9543468da95ed10037a,0xba7d26fda640bffea9f0,0x5aadb518d7d296fc6d60,0x77cf8e0fd150e9aa9866,0xca115b2116e530cef1df,0x1a28d889461255dce189,0x1bbb737750912b30d2d1,0x1c3f56e1961e44abd04a,0xa1b7ea22efd5fed83402],
[0xb1603b56e43eeca7def0,0xde0047ab8f88d0ae876b,0x79cb3aebefd00cfa159b,0x1e61443a8abb5775a632,0x9736687eb871d96ed665,0x74aa65abc02c7bc94fd2,0xcc59bd215dcd7980d05a,0xd972cf878c216ed74b1a,0xb6b31de09d4071468e77,0xe1fc07fd85837852c283,0xbf395917f9fb5f4815ff,0xc6da9713b22970abc224,0x353d20a23fe9b8d8ab,0xd201a17eaabb70406197,0x855f913a3dceb685d7b3,0x81775072f09173627ff3,0xdbb7613fa3ceab204523,0x3c6c9b3bf9bc101e2062,0xa76cfc0b5860d1a0c254,0xd266d2ac2c6d7c8a9eaf,0x4fbe01affe232b18ac43,0x878220038faec06da1f9,0xe5f921871d82a6d2241c,0x4028ad8c867f61f0b8ef],
[0x16bc09043dd03db33331,0x1161483151804353fb92,0xab665b7cbf3168935e2d,0x55bb10456829354ab287,0x531bd573daf89dec552a,0x40db448f0b2d1a02a780,0xfbaad95a694c76851fd7,0x38c400bbd60c1bf433f7,0x425fcb81f319f132ee36,0xd16b2d4ff0e708be0b09,0x3f1f052a17285151a818,0x7630415c1f2fae147b8c,0xdc2bd31be678e9c4eded,0x3107318fb3a572ddc0f9,0x5244346a87b81549933a,0x6e3251a4e958db79ec11,0x2da3f5f6c211cb228481,0xed1dbdc29e61fd02ff0a,0x9a9d87ac62667b187d57,0xc6c8988849881e21ac7c,0xb3f5e3f48aceab8a0656,0xdd5d85b4a9f82473892f,0x1225afce2a65ec9ac59d,0x3b8b579618c9ab3c9c49],
[0x4b8223696dca547959be,0xddba319e1ec89e088ec1,0xfc746abd58350c6b2f6e,0x298c95ef723e313aefed,0x23945c178b57e78bbb29,0x7b0c8854a21fd9a95b99,0x8cddd18d8861423b070e,0xcb172095da2f56221969,0x8510a7cc23a29ae1926c,0xdb861f255af47c9ffd0e,0xab9b8ffdcf77828cb281,0x8f58d358d4d3a77fd392,0xae845ecee945e7413986,0x7fe7bccc45b534019e18,0x8877319ac7d4c265c0bd,0x1f5ba57d4e86612d75db,0xfb4ec5fde7057fba503c,0x344a79068186f5362486,0xdf5647664d3d78630e66,0x5ac360051d2fd754a49c,0x3c2d0c5b1a3caf067b2b,0xe71142a0e904e98dce39,0xd933552640c4adcc5bf5,0x3cf463400cdd4653f357],
[0x9497e4722fc1cb895999,0xa64512cfb27ce7aa96a3,0x7fe1aedbe6389a779c7,0x1875f4290c6c03710602,0x35177515a28859210cf0,0xfe8e3e0af3a90084df9c,0xebc1530c489753a7f833,0x55c7a739993a7e217323,0xbe22e4a83e835e79f10a,0xf82b54b29a1bf1b78f2a,0xb5324b24c207fd6d3e4a,0xdd232358045d521f5bba,0xda17f14539e7c21b8df9,0xc48e2df621334606c2cf,0x3e20439e88d75e7e74f,0x2d445eebae62ebad8acb,0xbf6bfdc6e5054468ecac,0x735a4a9a89418a596c81,0x816095f180f35de38575,0xa524a75f205e45e3039b,0x9b8a6688ff644de029c3,0xeb690100ed2ba509cef6,0x89b281e7fabe8fb2f524,0x1dc536229e909de77872],
[0xebc230cd22efc795a192,0x1d4160e554ba4044df9f,0xf5a19d0411798d85693f,0x889582cc184563675470,0x59a9c008ac209c6d3d34,0xe5c5bfab9c480a0d4c02,0x4fc675305ba33fb4582c,0xc76b80b8c0c2fe9caf59,0xfdf841c4f780ccc962da,0xf34ac6372c232f00e965,0xf62dcbab033a0ed62607,0x399b372f9c4b84c2548c,0x52cfaf991e6f029f8957,0xca679d11b86ffb6be71c,0x4893598d816d4fc83622,0x67c8ffc4d0400cf50dea,0x9dd041488925e39905f6,0x30799862fff2ac87e4f3,0xd8e34c97e4c84a9f68e7,0xd37aabbf0ed0da2ed098,0x8dc57b6b9d02c3e8263c,0xd4c924ea58d49ab084ff,0xce2b3545b4322ea3a791,0x6eb5db4a65f2129b1c28],
[0x36d24af07f5070258b47,0x22cfe8cc66044eb8428c,0x37d5947120a685fec543,0xb2521778e96243b6d37b,0xbd4983407ffaa3be47c1,0x7ebba32940cc6085c4b0,0x2897a3b666a009fa1a99,0x913d47be44e3c0009ca0,0xd739ad3e4c05a5cb2344,0x32b1fdb543e7fee40ed4,0x407fd1beed59235df6d0,0xab00e633484a5fbee6a8,0x5b9e7935e4282561dc16,0x8107d7d14b9da89ae735,0x4236cc0609fc4e8677c7,0xcf001ebd658443d133d4,0x441d16d0c15b0226cc95,0xb69b9386e1f1c4e7b041,0xeb0d3273ba405ffd9c04,0xa251aed6d1d0934a2536,0x7cd49ac7db1c85430971,0xe4e56ed6633a38f85,0xa2ef89880c2a4e92268,0xce5426bfe0394539ca61],
[0x593f557a17b188063cd3,0x41b07de7d8aea035f890,0x12990a32b5cb185519bd,0xc585d5e4f4322c9c249f,0xa01964482c72d9bab10a,0xce58e4a4067246034b71,0x196a99ffe9532f514d8,0x418742f1b21f0cb7f4cf,0x945d3c8e9fde3eb42309,0xf6ecb0a44da621648d53,0xc306214f69f982b73306,0x30a9b1786971f00b3286,0xed1982084b62ff408d1a,0x3bb18c1791be65f65cae,0xbe5b3f789c38210a5f45,0x3e9c64abe614dbedb913,0xaade2a15e760160d41b6,0x2b9d67856967175ca49e,0x3b4926bd24ce2d7349c1,0xf4dae2950b907caf74b1,0xfe3f4c1a32efd689add4,0xbd906bfbf04e347317c1,0x991960b0d483444e704d,0xd65a1899e005e4b6bbd2],
[0xa40a8f89fa6226d630de,0x7e23c37d54234f659d42,0x874d7d4ea1d0d0a5069b,0x1c699fddac7904162dc1,0x96ea207ef5bfee8dedf8,0xd574886298567855a375,0xd5b70a01a60bd76b708f,0xae204e48f5a4827d85f9,0xfd22e33df629abfd3333,0xaedc9ef9b41ea7bdaaa2,0x14b78adc6ee3b6ef8cd6,0x6dda43c53ab787705121,0x3dc866041a34cd6fcf4f,0x669ac12ea0fb3d7ab0de,0x6578c139480be54ed87e,0x50e1cfa01ef328b6b195,0x712dbac439161ee6df,0x1dd5478c6f636b61c290,0xc66864939bbaaef2a206,0x9179416401fcf9a53060,0x2c364b9632a81680a300,0x51394ac98828cea528e8,0x1e23ad6006e8284fdd68,0xe469cd49bc23c9b9762d],
[0xee32bcb320989fed4ec4,0xe157758207dcd1d35281,0xb0ee8b7b5dfe688414e9,0x77b71a9079ef3573ba57,0xeadf4ab8ad2e0222b335,0x28eea226078cf26c96ba,0x91f09a45bf8d4d068009,0x5139630ecd7e60c34b2f,0xffc32ec792a7d8f74912,0xb95420eabdf272c38878,0x6e9f1b3336fbebf2c1b0,0x8f029a8c9517fae098c4,0x27cfd061a81fbc536fa3,0xc5150fa38861b8b6847f,0x19e21dfd28b518b417cb,0xffb30faf75f24cbb6238,0x726ef44b14bd4fdd1cab,0xafb94c6031cd79f87cb8,0x683209a20d253cdd8035,0x8f0f27cf52fe1652e7ad,0xcc87df9dff82f60d684d,0x7ad44b2a340d3d019261,0xe5edf04bb4ef4ac81a63,0xb03c848f98a7f2e022f9],
[0x78a5bfe76c725aae4c82,0x4ba51cdc21a35f0d48eb,0xa08dbe62df77e7f449ca,0xadedb68483c5385c62cf,0xd9c8e6e07a6f26ed498c,0x9ea88176990bd5eab467,0xbbe943ac9232eadf63a9,0x81ec340a4db0f3a99c98,0x6e404135797bbf5202ab,0x7a6136c06ab69f8b45f4,0x4c575aac9f72f305b648,0x784b92cb65c0bd69621e,0xe5c4e728e638e22faec9,0x366121447de30f04fef2,0xa74979f0414c299fc9d4,0xa3d2df7d9d14b0bf9e63,0x46849a278a49fc11df0e,0x7dcdc96777775178a023,0x1d7f69830e35b6670c00,0xf2bf4bd32d79c84cdafb,0xd0a300155b6a9c1d8bfe,0x34e9410a5d15974bebc,0xae15fec9743a882c1a05,0x84c406b358d34c0c1107],
[0x32467562ce23f71c7992,0x1145d65119754934d41,0xb6ec83f705aecd6de96d,0xd948c3c41351c37af4b8,0x4a3b208c0b896f44a3b0,0xf55b5081506885e131ba,0x55a109839a5b8ed29c99,0xa4f4c4c410b4154215c9,0xb48020035ca1740868b7,0x91cc45fa663f6fa79e84,0xdbfe5dffdb6274cc1607,0x76dc19adb52a31deb96b,0xef513b233b93aa55c491,0xd90fd20541c8da3db114,0x4cb0a8eb2aa2d0b4c02c,0x4a214ad158a20523041d,0x9eac9bcf90fcfc92c21a,0x1af1b33eacb56e9d49,0xd28bb0c2c84da48c9bd6,0x50bf6503d31f15eaa6bd,0x6f3265d9e27d17b43edb,0xed6300cc980fbb92b35f,0xa38e001386fafcc3a272,0x19c2b1094dfc9c184407],
[0x16e9d13ce695fd8fecd2,0x5333e6f669e11e4ccac2,0xb711e409c92f1a360a8d,0xe8e02dd8b861dfee585a,0xb2f2800b93ccda003d2b,0xb26fa7bf6f9a319f6f94,0x178cc2196a8a0a0ff910,0x3fa3207e110ec18c8aac,0x3d9059307417a2ffe4ae,0xbefa7d12e32128444b49,0xb6ec018a47e3cef062e8,0xfd784b3b28f17c91514e,0x89f1111c47f9cc987ac4,0xa943741ee920ec038e3a,0xffbe17afc204a14ba82e,0xfc6c1401f18d0ceace55,0x7310d52e01a8718617fc,0xab3326c5cec137011d5e,0xeb219bebfb3de4038e96,0x6a24bcf951ab084f39ef,0xdb96902c9238cb208acd,0x1020f256c5ae5e6884c0,0xbae2ec378151432384f2,0x3657722eaa70d1484336]]

def tile18 : List (List Nat) :=
[[0x3bf28e8db01a9a92be49,0xddba669c8bf90eb1e34b,0xd2cee73570b690102ae,0xf6b58cfd8e1f701bdb99,0x15ea743aec483e233cc0,0x5916de768d4ae3ff98a4,0x6c9798b5cbec817ecf94,0x13264a371fbd217fc6d7,0x25493aa216fe942c4a27,0x2177e374516e7ffd3c64,0x52fb8708bd68f1300185,0x529ff98e0e46bd8d0e6d,0x649e12f24311e8512f9b,0x32f27e09f51c6c1021b1,0xad14abdc61c3a5ebc62d,0xdc4be15254e718155634,0x5c558b775ad30bc5b305,0x718ab8beb6016b51081d,0x1c289091d94781dfffd8,0xc888534a3042f23a8347,0xa4b1bb14fa28b5071dc2,0x848d9c9ece0094e6018c,0xea1c8d1cc1d0bf99d415,0xf911d951ca746a52e7d9],
[0x32e7094f00cea63d0a77,0xe1cbb5c23568be01f6ea,0xb3c82ab4d614a83849ed,0x7de1fbc709b3d0e00eb9,0xec92bfbea1a9e8e3147e,0xfa5d1a3da8693d78d82d,0x57c86c2f0474e6675476,0x81fdb269b2691f334d1,0xc26c104613c114e053b6,0x9e75e9f384b6fa89888d,0x9109a0132100bdef8df5,0x3c82c11927cb2b68f6c2,0xa5f626d9338d2c03b668,0xd4adb6742b93009eb4b,0x9d7348eae3358a2d7c39,0xb42767d2167a1cde9112,0xa5be7c70be48a5db605a,0x6d80faf46e58e0140f98,0x3a98b79c78e574d4a6eb,0x7c70e90206850101fc8d,0xff9ebed308458a8f4718,0xec38af424555e8cc0ea2,0xfefbf522b175a576611a,0x32cdfdc04ef6bc90e9be],
[0x91577572a942d6046c22,0x989c500095a15881e08d,0x7dda5813158aad8be561,0xc45473580e30d927d578,0xfd1869e189f7a2576fb0,0x794ad1899d955311d742,0xbc296abaa34a3e8761b,0x75c529412299fd6a4cfd,0x3474726610e1c1f7676f,0x9168d1a8131cf6c663b7,0x368cc80e0974996bb51d,0x55ad02d28212ea08f821,0x75bbc000cd0d3beecdd0,0x72250eada332b41b6194,0xd6aad0954394e45c8b2d,0xc5784fb12a5e36368a25,0x7ea913a56cfb44d3ab9c,0x9fe06fbbcfe369ad7fc,0x3a43c994ef00c6c5b778,0x971880e44ec64a20848f,0x86df34a7859542dd7802,0xf7f0d60d4e3e78e2c228,0x2b2847fddc94c9de19ca,0x7b422f84f7d3acda771e],
[0x9ad1766108eac4b49c0d,0xc874b0c0e8def4fb21fc,0xa90084148ce54b452447,0x3293bcbcb51d6b194b78,0xf3663ef8049a7b935354,0xba546eb7e4756fcd0d06,0x51431dfbafa74b08452b,0x183dd65d15ce7110dd5f,0x130f6df134fa91368c56,0x60119b5be90185df4b45,0x6198ec8dabed17a7b370,0x671cbee767dcd6d1bcf9,0x1e660462966a5e0db0ca,0x3eab16031698f084e6ee,0x823bb7076d8691da047a,0xddc9b451a01bea678f4d,0xcce3072f1411df5190c2,0x92a96c059fbcabf2003c,0x10e6579f56b5352ce3c,0x879e442853eb729a16c9,0x4402792d1db4a2cef0e9,0xc1de7191cb5c462c2166,0xf77b5f36925d3124f5d5,0xbb8f00e40f3c1541e5cf],
[0xa10e70b41f4faffae95,0x33cfaa2ef35ec3d28674,0x325fb1892300d5572ada,0x34dba92639bc7bf90146,0xfd0a26f79b2c2700be11,0xb4ae5e26ec7da1689896,0xcee0ddcb8fb39560ea55,0xdf5f4e0813b9a9a5f2cc,0xd2b5b4a241e010a0cde0,0xc9c119c7fec1b6a798be,0x30026d059b180d5cef4e,0x5657b36379ce634e60fa,0x7f2ab5e2def2fe84edd,0xb6abcf68d179cb86513e,0xb8cea602e827cbf7bc73,0x9a80e4f2decd2739f6a,0x9582d0cfa97d817e2157,0x9e33f885df6a1ed2919d,0x8ee03ce1116c5b6c4d76,0x886c57b008ce443daf67,0xf2106da3e494e0181919,0xa46f75da1337969ee8cc,0x85d21733cfa9c8c6cd61,0x33d8037f46548bb01ba2],
[0x10b01b95ff48c1a3e4c6,0x5809c8edf3462d3c6144,0x6b6656897d2b838b75e0,0x5a7786c552a2fe950546,0x512c504aeb6679b5ea1,0xad65c9a6f1999516c1ee,0xde3eb50207979e3bfa1f,0x6fa9959ed0cdd80ba22b,0x97768b5341c1dd313dd6,0x3357c603a3bad35ed9e8,0x11742e70554f1daec738,0x17c519f3d919681d42c1,0xac5537db9683e8d56ec,0x2ee634eed7ebfebfd5af,0x90cc95115b5c4788c17f,0x7f66645c47063130c046,0xd5c14217a60364788379,0x4f92437869053c90e818,0xddd94f03d7f70364e6b3,0x70a83e5715ca63afd9f1,0x5f2c3368c14ea902c0cd,0x244894c1e29a21f7e58c,0xb95a90691abe41cc4abe,0xe2932c1d79d12cdd8a8e],
[0x3349481ba1ecea4c3800,0x909df0e0af9ba010444a,0x866a5f704d6308a7c9f,0x74c4d2793589b4e18246,0x5115b00d1beae3d44c53,0xd7e5e23cd8ce1fd2f8ec,0x265316168fd8e37a1a58,0xd82ee46af41ef3a6598a,0xf47a86c26e4033ce66ab,0x55f6103c6d9df98990ff,0x5523bdf3bc0407db216f,0x863cf77e744c8db2e93d,0x8bedf28fa60cc4a3746c,0xef4347a48f25e45872eb,0xd11bee202fb466cc7aab,0xaadc6583c797aff60a32,0x1ddd3000bb6d3b82bc49,0x6531a85e3b25e1f03d54,0xf5422e527f4e006e0098,0x58d12801ff5912c3bac,0x17172d795a00ca9f6e40,0xa9823dbbc3fd20da8601,0xcba867e19dc42694a0df,0xb129e4ad4b71778c5509],
[0x85fe242f5c09b9f128e1,0x5d34b6e631136ce22323,0xf884ae4cb4e0c376b293,0x9e45793f60981a4d12e8,0x6ae439b1206a1de3dc43,0xd565d07e2795734c67ee,0xd2ca6f6f4585bb10a7c7,0x25affab1143479ab0871,0xaeaa93301a37c7e14118,0x1beb7ccc208c53bd2143,0x5ecb99b47a7dbd33289d,0x94b29f926f9997f6b5ef,0x4e6eac2899b58d5a8577,0x5d86b19c6b72c4a61fee,0xde5f198d621780aee13b,0x67237a3a26292e7fc826,0xa1056cb42484b308d497,0x80dc99d8f087a63a4f0d,0x2e8753832f1c95006944,0x25555a8f501e5e8e062,0x36ff5524a57820489cea,0x64de7784214802a8ec15,0xf18920bccf8561768e54,0xcdfa98171d60d49ea5ae],
[0x356283ec67830965bf55,0x88722acbf66a7ed287c2,0xbc9fe4e6c100bf37a937,0x3fea8f336f8b06a69a74,0xed27261e7ed57efedcf8,0x498c1ca901d14625cbee,0xfd526374c0aea20b91,0x21c3b977c60341c63ba7,0x106ef35261e73e7ae807,0xee506ce40daac7f117b9,0xd004cc65f2d1cbc87903,0xc76c5783c65326b76a9e,0xd01d529f0d02ae6bb89d,0x68d1c58cfa2c63e09e95,0x7286e0013b5e328117b5,0xcbcf48b145735f5a876a,0x45255333ac9694614df9,0xb9074a8cc2fdab74f218,0x4232e7faa61986b4a636,0x4919e0e0284d72d3be38,0x30e474097916a6234a1d,0x5a7430041843649d8f2,0xd10169cf71e98f92b56d,0x36ef27672982cdf5d472],
[0x6b5ed186e6631c66bd21,0x1db8a27bfa28b90a9b08,0xf09c07149acb93b2d126,0x2d06a8f12469e3b3652,0x2f1d10e1309db65a4dfa,0x248729122f28bad9cfd3,0x6bbda44d8b206861f974,0x663ece88e3e96d50ace8,0x8e2d1823625bb4c5dfa2,0x27eaed32e93f2cc6960f,0x8c901e86889acc355af3,0x6ddf33c21a81a9c9d8ab,0x5b2becc254cc5866fb55,0xe6d7f002aca4e6546694,0xe5278081bd266e77ad04,0x4dfa201fc12803f3a48d,0x17799f83d10a87d2d97b,0x19b91ecc82a1bbcb8cef,0xd6118d9faa382cb1b6c7,0x9f2e88ecb3852649f9e9,0xe254fb98d658d119a8c6,0xd7c205e36a691963bc6a,0xaa326e8df1719bf9a20d,0xdd13bd866b9bbab690a5],
[0xb88ec6dcf3768067112a,0x39bd5051d6d3805e4d55,0xbdafd23256991c65658,0xb92e9c724cbaf88ffcff,0x6adc41e76e86c30c4907,0xb2f72f7f219c2526530f,0x5486c0036c6579144815,0xbbbd4fa59d0252f70e41,0x8f37a8d14162d5289e6f,0x5fb4baecd6f98f64ea69,0x39fb6ba045b11a245335,0xc95b2b12ea0fa7556627,0x4580a0e0fb573d8cabd4,0xb8daf4a902b2fbcd1b26,0xdd1136038cc381716d6f,0xe42be13aa3a924986d62,0x461e37e5cb14802bebb5,0x23ac4affe0ad363f8b46,0x4745ae8f0f685cd2af79,0xdc16032796f712645d5d,0xa7fc0218b7fee7a77245,0x39e6960d614153c575ee,0xe7e628134ea9675f31ab,0xd6b8aeb59b50e20820e8],
[0x694f2e7eb5c7ac25b579,0x3f5a0ec44ce3e70453e7,0xe14194071b8c826997fe,0x486a59910207a2c15cbe,0xdc9877720a6a0b6167f4,0xcc09b1d5ce94df31dfa2,0x6204def528094c91a5f,0x4cbc73e780c3adc37ba8,0xfc2d4ec5a885994605a4,0x6b2a8039eabcf713780a,0x18538bb91c0fa954f925,0xc6c2c378484febcf0185,0x361f12e9cb320c069548,0x6c86c13f1d396cfc741c,0xe6ae6cb69156d6d53a25,0xc5fc0ed8a1f949d5d4f8,0x4be25ae421a54cde4bef,0xdbad81e5d71e1dbd6af2,0x3e7264ce90ae0d4576c2,0xd8937ed35cb33977cfec,0xc5eca9e90e0c59a1353,0xb4e99a75afddea333bf7,0x29acd18df41018d5a96d,0xce3885b86705f46aac82],
[0xb3ef91e3049bd34a8feb,0x9745f15d12a61f185b44,0x576b497b183e1a2f75db,0xe90ae052c572aa8aa50e,0x33b4ef1ced5074035c2d,0xa7e0aa817b68b40ee5db,0x188654b9e80f08875ec2,0x2d85c987c4c363098bde,0x652765a59bd84c25a776,0x4c41da3f5dfd42ad2598,0x6330bcd198f94e5f420d,0x60e1cfd8d56aeac9b0c8,0x5141c9d91b0175aed65f,0xd12b5ab20ab29da1a045,0xdfa03debf805ae7b2702,0x50d977e3b6fb051e5f45,0x78c0810f321f0d18aa7b,0xcc74e1a651bebda64372,0x2adbae8ebc578d8104bf,0x2746ca1db565f74bb9bf,0x57924b7e14e3249bc1b5,0xda2a778b26a900c3f84f,0x75c84272f1ed9b2537f4,0xcf25cf7f290e69083b0e],
[0xbf618f5330fe6153d716,0xa21f57b6f1c5cf7e2a9f,0xb72fbf5e658c3559fb99,0xc2f6d6bb053c7aa53ef0,0xba4d2520d428802823c2,0x3b93e6d2442fa6e22111,0x783049a42eec5e6fd41d,0xc8502be3b23c33b657e0,0xa5e7fa8500576edb1f6f,0x5b2f3ba7d2baea79d88d,0x3a7fff9a2dbe1a47b205,0x735421fe54c1af132fc,0x14dd37498634507666c0,0x4d879d81c799f2bf915b,0x526cc6aff68e20ee5f62,0x1d8653fba959dbba74f1,0xc4c915176eca18cbf309,0x38c562dfa85fea47cb00,0x19b4ec94eab986bf76bc,0x8ac5e102af11368138bc,0xe9cd44d2f6b1e33564c2,0x248c3c37f2d310bedb0f,0xd3db38448d958c153be0,0xfce06a5015874470a880],
[0x7f0aa7abfaba1b7cedfe,0x263ba2765af8a0a35c32,0xe9bf180f902f5ef0b07e,0xd90b4d09ed8bfbe156de,0xa68310df4288f9d7ca1d,0x2dbd97101c2d8406f969,0xd35d9fce21a2281bc889,0x74d308448831063acc30,0x7ac43ae1d318e2bc682a,0x8fd0b4b7f915353e341c,0xaf97e3cba524a091dfdc,0x4549dd0b02e9f679cc33,0x8aff028346a07c28600b,0x85faaef6b757082f8d7f,0x738c11115fcfccc9e095,0x37e6a9b9d0a9ac93af53,0x5237e03653596c781b9d,0x5a56868681ba04f6698b,0x31bbcded809ec934a81d,0x84f98f316cd938dee177,0x51bf4095fdc42a5c0765,0x2ec5ee6b62f0dcecdd8,0xfc00b05d090f1d26c666,0xefea76e50e4d2ab048dc],
[0x248d5cd09d38342f3066,0x95c9053660458a43598b,0xa3f8b30a20f1136a5776,0x53d02c2189bc556e36bb,0x7b430792400be734a379,0xe46fb67ed753c2724f3e,0xe04f55007dd807987b41,0xbbf716ab049ecdcb273,0x1c89c977674659b255b8,0xe9cf9b75cbb73bc9f956,0x2ac3ed50ff1be16c0784,0x3082728d06b5739d0bb,0xbb5d63e3d36bf24a747,0x7fdd547fb28875da2326,0xf8c9d1c56cc8a51091e9,0xaf9bacff65f68bd061db,0xb1db8c0494938200c8cf,0xc2f92b6c8337f3e718,0xeca5dfd6a36d9ce58ac5,0xc8e87d65804fb69167c5,0x7b948df62b2e35bdcbbe,0xc55b0816bcd78976a6bd,0xd3abfd2db7c3573b2072,0xccb91dccb53aa573b01a]]

def tile19 : List (List Nat) :=
[[0x3dac9d05cb0440e5acb8,0xe391977c4f40c748a17f,0xf738dc9305e4718c791e,0x1b1f422cbe81c051b722,0x5efa44c81b6b69dfa9d4,0xeee96a0411ab74a9aed7,0xa97c9482f256da61768c,0x6049623ad27adc648f74,0x3dc10b9c17b0865fe54f,0x8e49d9af20f768e9b473,0xe7256112fc67e7a8c2ec,0x4107eeee819e879e65ec,0x718f923fb1b876cc8c6a,0x69171bad7d0fde6808d6,0x6cee11a56b2713e26d0a,0x3f289b1ae51d3f21096f,0xde6576a99015c65bcfd4,0xc1917808a64957b4625,0x2533ece84c81ac54fc8c,0x3af316c019a5a6b57232,0xf6fe146aae01b842a996,0xe53058ca3ada60986d90,0xb6f9628e9e068caa92a6,0x21b5805bcc0519f966c0],
[0x6aa8e7ee1d16e73f51e5,0xeaa51025f652a73d5a4c,0x65109bae17298c21046a,0x7476103cd50a605eb3a2,0x13754b53098b6be10850,0xaee94a72f3bcdb0a7393,0x111369df67f4fe36f25d,0xed104397f8c3e467db68,0x4212f18ebaad7d77cf0d,0x52f736a0461b68a12fa2,0x95413de27c7bf3545d51,0x899910d2f7c8031003f0,0x8f8e46146a99394894b7,0xc3ea336afe1dfb44f336,0xd18e7bc7c3c8631b622e,0xa2a351988fdfcbda78f9,0x773ea7a1e161e472b8fd,0xa9acdd2fc3e159b65c05,0x576bc5188d804c043d1f,0xfeb69ae5b6357f2795fc,0x688344087544450e33c5,0xaa6d5eb9ca2d5d8c322f,0x3acce33832de14b666bf,0xe02276abfe219871eb53],
[0xd20a0ee3157d64bfebaf,0xa689bc85e1ea0a280721,0x8f3f0af76ba00492e0af,0xe4636b59a7af35f371f9,0x36506614bbb280ee9075,0xa4c81a508d23fc7ebd2c,0x610c3be1bffebd40deab,0x186405da49c2a4da714f,0xa7efa9b3bbb534a15f92,0xc2124c18342ad39b6169,0x9881f8f8cf383622b854,0x90f78b6397495b2df965,0x13e3241b7400973d3e91,0x8ca8debc862c9b45794f,0xfe5ceb592b8ca1d656a5,0x8247f3128ea2fe5fe9a7,0x60b9f643572cb4ae20aa,0xc81458f5b79733744627,0x6ea5b72b175afb30ca1e,0x2807e58420f7bc1e8b0f,0xa6c0314a876d6091012,0xe0b7170baaaf1c316738,0xbeef02e2b1ab60f12d09,0x62d585b2c1db17c06616],
[0x6cc4d367f3f8448a6b6d,0x3399b1df1f9034a9ad03,0xde41ffe44ef81b2bf5cc,0xb07b41e4a9ab245127de,0xb92097f6faa8364adccf,0xb4667b5bd99a58e75a89,0xb043b96872e5b1a52fac,0x3d2a0e672644f77888a6,0xd4f9065afd2480162895,0x2afb81fd17d5a3abbf0e,0x172d81ff5858b7c8e345,0x6285705d7c2f23176ee0,0x36cd517e25c9551ddacc,0x9eb42059c360a8d89575,0xd62d05500a14f9770707,0xd82c1bc44728f7bd1e1e,0xd5d5c541a03932dcdde2,0x37cdc257ec3dadd27975,0x245873a18660d82c46d5,0x37a689aaa581722d42da,0xf298da1a5745f3e9d130,0x40676942b454b89543d9,0xd822a5bd0c99ec3d4e95,0x26c4aa77777c1e28d10f],
[0x6566c7fbf3bf0619864,0xb41d6e5993805c88da84,0x3f1fafd9686c49585e77,0x464f65ba666d259159ff,0xe6dabdb9f5b4bc358a04,0x527dafff71fcfaba70ff,0x19276d091779ad42553a,0xb2fd91ffa31c84b96845,0x33a64f5abd5f0dcf1a14,0xf5f001108340f0c27754,0x8f99862d0293802305be,0xf82314b99ab18f8582e6,0x9264fd63e74c744e41f1,0x7b65c2355ed45bfd9f94,0xecc594fc7e2eca76bc63,0x9d65a20ab1ee25b6f137,0x40604856c35912c33ebb,0xd837c5a1f21dafeb3678,0x9258782aaa8807c96c7d,0x97e66fb0e539f2621864,0xcf6b067bc9433d171435,0xe2e80db68bceab080726,0x8ca950b2380e7b60effe,0x7cc49d2f9e4737394649],
[0xb86487cb7923dc955550,0x9e9cc13b705acec74bc,0xe857812de21bd6162517,0x5688b59a2a3944e24e76,0x9ab8c520ac97e35e7b76,0x5d7d5afb0f3e20498785,0xdfb0473925f371fbc1fa,0x62645b00cd228d0f5df,0x150b873b1347f4207c89,0xb1bf9733d08737d6bb9b,0xaa2220f71815b6896bad,0x2098df89c1f8bc54797d,0x719ed26fad462a603004,0x8c7d4fa8b98d4f72ea0,0x62e42080209ce67a71ac,0xc2eec40647de32c93e32,0x29a4bb5329ac0d14e5cd,0x122839abe5be79647128,0x335e9656a637f4b3efca,0xb6b1b8c0c5da09d3cff9,0xbd2b9efce0d9f3099d4,0x1eb71dfa27918c6a37ab,0x469060c6d97915b8cf38,0x3b5cc12f950195d60d8b],
[0x633305a425f45b52b9f8,0xdc56e7ff16897917ae04,0xd6d92d735401ab61f6b7,0xe04919492235f4705d21,0xa6910985e1acfcc24c65,0xc0cb78e18dd21e218fce,0x8ddf79080a93799f5502,0xd56c262c53359c593e63,0x561a2346647990130aae,0xd4b25df573dd5f66529,0xef181d5c2bfe950e5ba1,0x3f4274f1a0e832ce127c,0xdb9d0ccb244735471820,0x405ccee44f5d177a45b1,0xc5c19a445003c45009cd,0xc1eccf25bd12def6d118,0x71ee76a09cc0fc006f48,0x4c6c66b778c1e9ccfb2f,0x8b70b9924249339db694,0x6cd74c5eb980276b6460,0x8cbbc92aadabc03d136,0x51e56f3bf57cc08c42e4,0x31e68ddd9f12f8125edd,0x76f2be9e8c8693fb61b8],
[0xff9193b6f8e8366dfb3a,0xe1d4eb5d07d820af1de6,0xa41dd4d47c561afe998c,0xcc06e949fc28b59460ba,0x58cc56fa9341c36088f2,0xb2fecf8049f8b81595ae,0xf4742ee86ae10f13c624,0xac00a019201e38a2bbdb,0xf205a569393bb940b57a,0xb4c7ffe0b1bd54ac981a,0x7f25a382797182494053,0x8c55e43ef4ef2d1b1066,0x23015d17a24657209c4a,0x16b4e1184d9a16ec1687,0xf8e80a73c4d3ec366a24,0x2c1aa1e2b9fa2a2eee43,0x244b2472598f8ddc23f9,0x82bc0ea111e9df381f66,0x8e3c3601a193277d97bf,0xdabc861b34b1bf09ff04,0x8c278a63c38468060539,0x17becbe1aeda4d9cd7e1,0x1772c854b65bd7c322dc,0xf7a72d28a590b4e2514f],
[0xb86ad785c021ab302889,0x213580f7bb8ab16cded3,0xb47552c0cfb73c65dcca,0xfcbbd3e26503af70fd10,0x7cea5771b2e72a7f5771,0xc8313eb0412b47c7b20f,0xd3e1d1496d46d8cbc4d9,0xe2cea7e455e8fbad458,0x1cc73e2edb6e7df670,0x74c683b2608693dbd3cb,0x8bb0dddf36a452627f5e,0xd202452c9f76d2b3dd67,0x67379f4eb38712c32640,0x60ca43ef5a1df4779b48,0xe1b3b96d65025314e81f,0x737d84ad4ee988c4a7ad,0xc23309e15803e3063f95,0xf6d1c4e7448dec0c2fc2,0xc02286b0dd0f9dbdb2d5,0xd3edde881143a8903732,0x6a281a9f103184c9907,0xe64a74db3777b4b4d339,0x7d3973c8d4afd51f6afb,0x8ea5fe45d67086611fd6],
[0x8aa9aeea707792e8c27b,0x385971cb7000da5f6ab1,0xdac681318d55bc5781be,0x3f372db7201a136cbb75,0x6b41f5cb722b9d2bd5b4,0x17ad146abce11958c03a,0x55092ed16c56d25e677a,0x6d5340c700bcb991805d,0xd76311ddc72172a1aa61,0x4004218935392a84ebb4,0x7f7a906c030c03b0cf00,0xfdcdd0079bb3c368fbc7,0xcac552b8000d95a14736,0x154d3f37ef98a4b84e93,0x1afbea367faed268e2e6,0x4141607270e4cc65dca3,0x8166bcf9fb1d322d5ad3,0xc0c684c4efa37f3473aa,0xe817b0f0f514316cc451,0x13f17753dbc37abe1920,0x90376b65d3bc4b121b2c,0x14a90a10d243625d6722,0xfba9e09eef2710ed1bde,0xa253c9eb087a80b02edc],
[0x996f198a00cbe3e01abc,0xb938d842f2d9d7532f8b,0x46af629353a7107b11d0,0xa47a5d440df60f158f78,0xeb0478b943822ec74f71,0x440b3133e0400a95418d,0x26a2c7217dc7b21b88af,0x367907bced47ea6fcb98,0x345f7e6b2a8b40b1326b,0x79eb58294f6a822d9713,0xd4d2c8533c0fef311fea,0x67d27172c4172ac55798,0x2bb95249ed8782d47a5f,0xd9aed7f3df3c619b6bde,0x7334bd8d22a8a40346df,0x7a2071301202b2fa2b5a,0x8e2ea7ca0fe082015209,0xeee327de3959fa0a18c6,0xa0fa7f463336a9fff2ce,0xdcf50db9e87d57ecf782,0x25bb494fadb59701ad94,0x3df53ea4d1f17a895fcd,0xf28c554d7182ee05df29,0x68086d90c1ba0b32fb40],
[0x5e8f9313893d05855f3,0x6d9cd1eb60e035e82047,0xea37b96db8b42883e920,0xd6c2b980ffe8321be0b5,0x3d355dda0ff68958b70f,0x14fe61ee6cc223671f63,0x6668a1d2fff7e71698f8,0x3be23436b596b8fb7ebf,0xb1f40fc5ee13f8955f93,0xcec49e66c366e47c46f7,0xa8d86dcbf31698b36b0d,0x9e80c893c9980c8e9f63,0x5f9bc7f14ade3ccb5003,0xac1a6f41f31cc6a32e93,0x495c43826e2567020dbd,0x18d2fda00fe3308253a9,0x76f9a627ab190e6dd84d,0xb673f4f347b5315bb44f,0x1a9e816c281734bc3a14,0x83a1380eb34da0ba9070,0xcdb3434f17d7725608f7,0x3856016b7e26253eed20,0xa61cbc6dab1bdf4c8782,0x2add076680c5cc8f9f4c],
[0xa12a0a74e4a1fc5ec392,0x6efd8bf7c5ed7caf6ddd,0x6b7b9ce21f083ee4bf99,0xe75ce9542ae11be0f783,0x85c6facac9d1c9105f97,0x8d47eda4b6e21d72cfea,0xde9c9ca138bdecb6bd58,0xf8e681762a21fe1d4593,0xad35debbc1dd65dcf7cd,0x8c2f04817a808caa0e33,0x9e6599c80204df189655,0x1c91533d3b638deeba6e,0x420de80865e5527228dc,0x6c736a09e51dddd99f66,0xa961a771518ad468b731,0x830f63fe31e06c638704,0x96e18d3167a8c7910356,0x6ed7706b82f297b31669,0xafc5ceba1d2aaa668c21,0x5ea82ad971ca5e39ba18,0x551b7f0d0e07160e0f16,0x1008db2318c4172068d9,0xfa7e6e4dc2370e6c6dd3,0x4f000974634abc412485],
[0x235b3465bda2fcef9691,0xdf7ae9cd7a5106c406cb,0xce05465c0724c24f1a3a,0x3f3202056a3c0b5806b9,0x4c61cf727f3a25a07d4c,0xae8aaf2151ebe2d40b57,0xb2d401428cb72d8998b,0x95964303b0469782d3bb,0xfded63d9355846b6c9b,0x456b4ef2c6881da11542,0xb327fa7a966e7dfd01ce,0x679f93f89f67637d917d,0x4e0e6d109d84051f8f61,0xda6649cf884b24600480,0x8893a4ccf15766e75820,0x6b9fba801071a3dde4ea,0x3b21e13818f075bf836,0x47aaf05bc9aa00282406,0xed5e21ed1526e087d5f0,0x4d4fb284152cd5e698f6,0xa88c74d4023806176788,0xad6dba429d770f20b100,0xfb1db3e064e89e3456ea,0x5d55519d391c3d48819],
[0xd171079f9c2dd6582d35,0xa95007858b7472501bd9,0x2298cc86ff08ec073298,0xdc4c9170345ab621657a,0x26088479275b8498ae72,0x16adb7b098f6223df1eb,0x6c35fc20c55a34004d18,0xaada06340a7b1cb7c674,0x6186cf43ae6930f9c0d7,0x4e51b2edd52dddac5f96,0xfc404d6a8750dd8a25af,0xd122e6567477f72ccb97,0x199dac9ce49f63d576cf,0x3f680a6a42c19fa7ec46,0xc570cb5302e4a9be2619,0x70f1cd4c3b1fea97e591,0xefa8161e5a5c59384917,0x20a7c42085da700b7c75,0x87360990bf1dce45c217,0x32ea07ffa0ba4e4ce157,0xa055af55cffda855cee3,0x18940694a46ae8150e0a,0xec26a731392c430de646,0x9a00cf73d3431f126db0],
[0x8e018ee9d40b38cde659,0x42738ff6d44467f1eb57,0xcd3a2058337fcf5cdfad,0x282647ec986ce4b20331,0xfe3dada0a2ecdda84ace,0x3dca307f5a4c23fbacf6,0x33229b95f25143a631ec,0x17311cafe3308967d17f,0x70287a5204ca2efc4272,0x908c17ceb2977d7c654e,0x4a8f62241c9c009ee74a,0x48d678af096c88e08bb7,0x735c4ba180a68273cd54,0x53d3e3da4e73f8b3fa18,0x2dec9d18d77a265ac5c3,0xd28fd7d53d720d230599,0xfee4f12cd36e642a39d3,0x83c9b9aefbb761a98b47,0xeb5d5d9afbfc0f86b38f,0x2de74b51c9709a003864,0xd63881cfea7674afc47d,0xd80e8e147fa7f1a47875,0x8a0a7ba141f61c1a50ff,0x9d5e1b3cae3d05f73a9d]]

def tile20 : List (List Nat) :=
[[0xfcff720fe2fcf1efbe26,0xb4a0e5eaa4652332887,0x6e9889ce5dc1518daf47,0xe380bbc3a5ec9f8c3863,0x52f19bb1f0e56c1d88a4,0x8adfc02ef3a968f82bf,0xd9df85edc25a83b79c4f,0x5d0fa28d0971e1b10e53,0xb8cf489e3404638c0a48,0x51514ad895bd03247802,0xe88f7edf5487c4bbe5e7,0x87b0eba7bf09f9e69256,0x827c00e41689094a0761,0x6f7e07d951638f6f6acc,0xd65a497bad9aa7033592,0x68677e96437af3ba4145,0x12b6e2e10b428e6241ab,0x6d683ed7119ec2df342c,0x33c52911675f9c18801d,0x7a1feb9a16b8a969119d,0x523be278082ea5104d71,0x163c6add16c4fb2ccb9b,0x7bb3456f30d7b1e0b886,0xcc694e118eac45299494],
[0xf0d10228c64a28917a54,0xa1083ca9e49b30dde714,0x3c4e303c46d05bb7d5f,0xcf296d25c38f237562a9,0x3b3e2e366c6e6fc12963,0xe6325b76270b21bc3362,0xb70189ff701b7bb04f17,0x39358d0982b5dce48b7f,0x42c327413e4e6565687,0x92565561cc630b7fa49c,0x2e7b44c69044cd4e2dbf,0xed2d8449908828cb65c6,0xe4393ec5ab63495f5c07,0x271b4721f22e090e0996,0x658b7ab9b550fa601b8a,0x5514c42a5354fab0459b,0xba88b6de3d606937fc15,0x522dc66a176de47f466a,0xddca34fa2dd9a4371a79,0x9de090dfc88830701fdd,0x924e00df524164381404,0xbd95af55648b2c9003c0,0xeaf855fd922b63236551,0x2387dfd45296c52e820],
[0x1aac64ebdfb706bb5635,0xa8001d072013999f1657,0xd872afe1687a0f5c8977,0x46ba356b7e2722e4fd6e,0x5f7d50727a5862f07e26,0x3192bcbfb47baed846e8,0xd526640dd3e241962d16,0x447acbfc6b5848bdfaf9,0x515616f320816136f9d5,0x2666bc774db10cfcb663,0xc26a98eb58685cde7ad7,0xdfcdbd10b2edd55aa273,0xcb5a8af09e362c11a248,0xee6b90a03f8880515a3e,0xcfc64fa50ea2bfa30954,0x32fc284a12be1790a172,0x4108f76a0b90a5b4aec0,0xd668ea9e1a57a9d911fa,0x2ac838cc65a26d057d35,0x9ebf0220a560d7898277,0xd0c09abdfd3aeec03a8f,0x291be4389caa1fd83eff,0xdf9c8ba59b51ff73ad4d,0xaf0991f0cbdf2880813a],
[0x39056bd034dc1899edb1,0xb0cc6225ac68b0b65805,0xe80579f50c89cb698542,0x7b7b0baf53c30f7a09bb,0x89dadc12060d73901dba,0x488377c0261066c4af01,0x4ed56868c36aad58011a,0x1e15c66fe10a29e4af46,0x448e4f38aa44dbb5aba2,0x9949fde38ede876fdeb0,0xb7342dd497fb58e0e6fa,0xec19bcfd7dbdb831dd97,0x5b8abe2df74104553a2c,0x8869166b09cfc9ba3eae,0xf13c28168be4cb65e7ef,0x2ddc9efe3f82f752583f,0x4872c98d119bb91eb8d0,0xfb5586e0b0bd893292b,0x1b52ab777be327534ada,0x2f7c84cdcd6b2f39251e,0x63c1a1d1fb7376e40b53,0xd0771afcd16072bff9d6,0xa08978a303a5f88b8e6b,0x9c8dcc57a5a715bba719],
[0xf38b31f312fc726076c7,0x7ab486650d52ab2d1df6,0xe1b612d9e88b2840c307,0xfaf155586a022d7b2eb8,0xc998a200b8f3f47c5a11,0x371ba73eaa34d39ecdda,0xac623985b67bb9fc4d6f,0xfca0d8b5ef620730ec0c,0xb0f1954308f0e023b626,0xaa1f07361d304b2c6c8c,0x82088ceb2186c9837a8e,0x35a26e273569c08c19f3,0x8d502ef69d0d7e8e9100,0x1a9b84e031d8439bd88,0x7fe2a0a19e3fb367cc2c,0xb2bc782159b4653691f8,0x873841d7b7c44efe63a8,0x32a24635f7db7f43fead,0xcdd2dd16a5814e732298,0xb3668a6bc5ae57bdfaa9,0xa2710c9ced079aeb1a95,0xeab3baad71eeb9f24e62,0x9bae82fdb9bc970bac0d,0x92ef09936701e2d99bb0],
[0xed4651699a1d3b967ef2,0x89ba6dcc38be14a774d3,0xd81f3e84a46d79213ee5,0xd0ee83bf6fe2072b4351,0x9983c8e90a935345facd,0x307bf75f4b4783b038bd,0xac17d0a693335aec1fe6,0x9e556e360bf6def269d5,0x41dcf490f354a3d0bf55,0x57b88747a6254bc0a0a3,0x8b0ecd69870a367f3a09,0x30001fa01250bb2aacbe,0xc891f990f57a17b1c962,0x30a7b9c9e1ac64f5f36a,0x7adeee60e6675d659f3,0x6281cd08e0b09e09367,0xba177d9f1f92f5c73fcd,0xd3659fb796361184e10f,0xc5fafb6558816c0f2eb0,0xf4a0b09d2d3f0f96e477,0xf21cd7b11ecdcce5b26,0x86118a03f4a3250dace9,0xa28ba7ddd83ca179b5ef,0xbb83e496c2682b6d1249],
[0xf167f1403f2832ec8088,0xbc3f1bd1904a18a5997f,0xc7bc16589c9ba1a97a5,0xf7649234c0cfc0e6b937,0x135d8182f8bdc9f9b031,0x33a6179364e82706ef9f,0x39b7e1a8a85bd6e70588,0x2e577bfdb041e4d4bc96,0x4884e02e01b8082f4a2f,0x3bc7430c9b784cec49fd,0x1b16caf13d81a8b486d8,0x46ce1773ca4636270853,0x11a7965425ce7f1833e9,0x3ff78a8d7ae2eb4d6492,0x2c499ef56a3e2e0f2736,0x5467847d33d52a23fd59,0x2a00a74afbadf9f63767,0xb2606f6d45e9ceb5769,0x17f6b23d6d60df207e28,0x237abb11832d9aef989c,0x59cd9128bdc5ca5200e6,0xc739636fd61605a2ab96,0x9bd62fdb2a1773e10cdb,0x1bb2b232164313cd4761],
[0x5a39e8ee070bb2e7d03c,0x7ffa8142e05daaede925,0x3d97d578d1ccaa483254,0x284bcbad4b96625dd6e9,0xfc108c103d2e96801a7e,0x70de4226ab262feb42eb,0xc014b560a7f4cdfcb5d4,0x5db77b458489e9c2d73d,0xe2d8ff2059bebf25b4e9,0xdbb5791a56f375bdb262,0x4487db398a88ab622e33,0xdb3481f044849d55739d,0xc8380443c2877dda3771,0x4da59a3307f2caacfbbf,0xa9152e1de5056b7eda5a,0xe447bc00eebaafaca61f,0x8225d4e31e659b590824,0xbfe74925f5b163a945ff,0x4aec19558b8059332505,0x4f0fa873b3214764a05d,0xdc351e68191f7f764754,0xa2bd9c66d0e2d3566fe6,0xd57bf8739864edb71590,0x67dadf841ac3863d320f],
[0x58fcb8a242278eb1472d,0xbce0d5ab386617199e10,0xe792d901f1e2fe756866,0x48ac03d404d0776d0403,0x2ef37eb3ee97aa8d3b71,0xc20e2562867e95276df4,0xba85d26d9a6fdbf32d8f,0xd2175b9ebab2b15a6f44,0xb5d36a7886135d49918d,0x3b52236dcbcccbedfb99,0xcf21c2d98c44559d75bb,0xd0262f3a6f9469b40422,0x7b01c8b4e8181a681cca,0x5d021bf1c1db516a546a,0xdb405b717b008d41b69a,0x387dc101882b204e0df2,0xeb7a2ee69b268327b541,0x24980f9d404a72c17889,0x59f55ecea69a608d46ea,0x25932445aa38709b33e1,0x8a00284f47de0a36f9e6,0x12ceb228e975aa3b3627,0xa0dd41e68c9d08551f9,0x6bc562edda63d7dc274f],
[0xaf8aec3b2c07e6c32c26,0xa9767493f536b21a6296,0x7b334e2e1e0c30733fbf,0x3ad266d5b25728a21c76,0x8246910c6c001738bd71,0xb0b939575324b7b1664f,0xd6646decb25433e725f6,0xa6b6537c96ce99dfff92,0x1b1c216bd6efe2abea85,0x102f2bb5a5de630c5fe0,0x192c5a356c4812b402b5,0x48cbb90a1e229b9620f3,0x31e12e87317ea2a02163,0xe987d77c1b8984e7ad8b,0x7446ddd89ed75dea667b,0x9f7f3220470196ade045,0xfade6f864a3b6e8ad9cb,0xaf2948a31bb04378e5e4,0x38ed556364f8907dc381,0x1c7e6fcf3971c40988d1,0xbbb471980c1da9713926,0xeba5014f21dc77b05cc,0x8fbb61a32dda024a3834,0x353e6bd498efd6d49985],
[0x1a8169d584cff42363fc,0x3ba30521dcffbbaded59,0x58066780c0d0f790f201,0x8893ed468f47b32e72ad,0x2d2a76e9c93bab27dddd,0x54e9f53aa1b0dfe98f25,0xfa71b3770598f68e2ed3,0xaf684d3eb12690d689aa,0x6adfdea3fb6bbfd4b4f8,0x7da052bc3caa65de59c8,0x3a163f6618b148059691,0x38ffea18ee4b77001f8b,0x17b5eea9c2b1e1c10b65,0x3b87ca5a355062919901,0xa1a600eba0fd01a3c50e,0xbbc40f4a47299cd6378c,0x65ac95c39abd2096e1e1,0x22820b6f91607d598d5f,0x30cba590b0550f1ec4b9,0x63972e897490bf0ef188,0xdb20c4217adbfe6d0b54,0xcf844d99be017672193,0x3dad00a9464983120570,0xc6a16f9a1a6def7b6403],
[0x3baf2bccdca647d0019e,0x663514322cb03c3221be,0x762f8df4d36ccf1134e0,0x5015a69950fc631b573e,0xb26d19e40eff27cec705,0x1ac71b1a34287e403d41,0xf8a2bdaf4f0459e4741b,0x423e0746d3752666d85e,0x12cfd35bcfae20ae8500,0xccfc814f4e3e56ef01fc,0x3a4b75af5f9481a7852e,0xaa9d83e05bffb6c4944a,0xd49ce31cb6b669200bc9,0xdd788789cafa7f445209,0x78736d4fd21d59db35b6,0xdbcdda9274babd62b3b9,0x82ddd5b7f427a361acaf,0xc770ac4d30f2a05bba15,0xed454273a277b67efd20,0x30b9b2445a8bd4eec9f4,0x812ab81747d6dcb2a5d1,0xa47c6c8012b994976f3c,0x328211da4eeb64e1c414,0xd0209673b9c67ebb10de],
[0x4d7565c70e6925207bd4,0xb4e1662041a7325f4c80,0xeb750394955ac5d23d18,0xca1005b3c1d97b0f23ba,0xd8af76f026d9b1afe7b4,0x3d3c14188b27f75467f0,0x39aca41e2f2a8563851,0xeeb89c2fae5db9422be5,0x5ae0d8175f2bd86fcdae,0x33c713652a438268a933,0x4ab4fac16438a64aa1bb,0x82c65c796fbb41d11900,0x10296503e53ddd4e64c0,0xfc17efecedba81bd9058,0x929e4cba290303e317e0,0x6f1e31d5c6437cd5291e,0xcb013ff66112cb01b0c5,0xaaa22816947a8aa3178b,0xeb390d4d7d9822ed1fa6,0x10bf5957a67769696c8a,0xf48645cf506775fc553c,0x96a27dc2169af57251ac,0x6c1bc90c00424c68e941,0xa753a9e83474cf3ea521],
[0x8e95362dd38f64ddf3e8,0x69501f71e8eb04288f43,0xe80221acfda42fa8e83,0x11653fad1d2c6d6162d2,0x5767b16a47257cca95d7,0xfd8a5d73d36493bacc06,0xc890b32482a3e5c1d658,0x53c796cbaf292418f802,0x86fe625a7d0eaf00c3db,0xb89e2de2a3d4ee2b819c,0x6ae4829d0f41c911a9bf,0x6f01498f087bc195a4e1,0xd01955d61c305688f522,0x9fb4efd059ba9c07ff6b,0x302ec1b2c1f3075a8079,0xe42755749240d9717d00,0xa0abd8f6ed1a2f85a4ce,0xbd990829110f2711ccb,0xa7a3825a4339d0df01d3,0xc5ecc6d51f6e243f8a64,0x84d237e974cf6d464ff5,0x3e953beb8be6e8446b56,0x32f5361b3c8bf5c6591e,0x35b697187d0b87fe2af1],
[0x6c39fe80849d736bf11a,0x42a9f72b08476222e09a,0xc98dea6cf9b94335eb5c,0xe55e278d4b40f535b600,0xa61a2132a5d458a48e,0xf73819c6f2ba8c7ddd3,0x5c3fb1e55994c2236c63,0x87c8bc78bb87f36c62a3,0x1d2a257aee45bb4c05c3,0xedfd3592244d5abd64a3,0xa86f36b8bc4b42c10830,0xa840db169785d77d824b,0x8b37c5ff98924f6d1394,0xeabc7726cef9339eeeb8,0x9bdc1400a0a832cdcf4a,0x325e0fa2ad026b6dba75,0xa58f8bfe5ac17432f253,0xab8d84ff53932cc444a8,0xc26e3e8af6553f906d0a,0xcae437e5489bfa710884,0x244e147d431049f593ce,0xe750b1592e29f9a0d44d,0x2157535ff7bb8e06b40b,0xf48b67fcf86c89a1957d],
[0xd2951b929c3d912c763c,0x405b38829647c243cb88,0xb76449b9c7e1ce8ce430,0xf0cdf47b97586f9ac197,0xeb737eaa0e3d753dba9e,0xe14f8ea37b0a04e9318c,0x7b624be0b97371d80720,0x7444eda3a1d410537b43,0xecf290200d14abab94a,0xcc16d10338cf4bacfa16,0xe784987b7e8b64b2dbd8,0x1613ecf7a262e97a7fc6,0xcfc797e5a7c3f104ced5,0x2ed94b32636a96b5f858,0xd26216cb4be11678f367,0x30ac84b2b26ee1bb8ec1,0x63dd4213cc16318e6bea,0xd7433ad0e048228985a4,0xd875dbc6d5d1ece6aa0a,0xa310add93f1583848cb9,0x4cdc6d2bfae7d8a55a49,0xa810bfa2d4f7b12e4c6b,0xd60a4ec79a4bda64521d,0xfa9adc60d714a873b779]]

def tile21 : List (List Nat) :=
[[0x6645d1ebfb649adf7a57,0xaab03bafd88ef3081400,0x5dae25524f7fa8c5bcde,0x4d9e876b37ce5dd9097b,0x76f7ed8c306e590011cd,0xf667cfb40d5dee921aa1,0xaf46f1f0d95050405bb,0x929972bddc92a06115b4,0x1cf1e59d218703bad881,0x974fd4e8d1b3e3cd479d,0x7b68aa6095471198b3c9,0xed7ff945ebd1f1fa92b2,0x663f7225fa4be1eb874c,0x3ea62cc252729c124a28,0xc2311f4807d0e5c7499a,0x3fad7c1e064c943b5a20,0x827017474b55dc4ce51c,0x411ac4096616211847a2,0x3fafb4d46fe27f6f0775,0x260b70644197051b2a25,0xd04c5cc5de3ea794f393,0xd87600d808110fe2b7b5,0x4a91467e7f1bbe8cc2ce,0xe9cab2aa988cfee5ae29],
[0x21d42d290a0d47aed98e,0xa0cf515e17e02397825a,0x6921dda0c59533cdd57b,0xa25f6a7c24fc46981767,0x4f32a8a8eca6c73b9b8e,0x489463c1156519949fd1,0x51760a52204d112ddceb,0x512ff8127df0cd044857,0xb4e49bbc6879915ab9f4,0xdabf7fa57ed0d1979d94,0xad692b7daaf7adceb69b,0xaa86a9180e81efe0fbf2,0xc07e0cef90079407a4d3,0x6f2132ba3bd179bc8cad,0x3adfff18e8eda23d98b4,0xd191b548269808742b3b,0x1fe0fca284ed4d0c2967,0x1166f644750455330f64,0x684aabdb66dbdbce9c68,0x79d00b25a806007bcb53,0x265519505068d68f9cb4,0x3d287529965eb969ffe1,0x4b5e01a7fb45e971a563,0x69b58e5566639ac9159],
[0x43cc337cd545502c9a27,0x9512380eb12d350575f9,0xe22a2232bd18cc83e601,0x3ec4a79032a738722696,0x63d61b22b6970f23302e,0x5568f6f154aabb62b3f9,0x5f9c092a4f8688adc032,0x24fa85f96abb75916b9a,0x2816d02574cac23b08f8,0xb3c0a97e78e9fa37d708,0xd1b64b1d78eaa4122f83,0x218dbf03fe726cb6cf65,0x1a5301b9c8f2a771f491,0xdc69b4bb5319f9375455,0x3dac83ed0d460a25af66,0x334fcb2d380a0d4fbc5e,0x5cbe8f934543ee1fa8a0,0xca8e84fb428641f9ea24,0x7c4a179a028020bd0a48,0x5f583b2228bc5f344d85,0xd29abdf1c87d71f8d196,0xef5da858f35b4cd275d2,0xf9a595f4493c5f9f6cd9,0x8761d58f628b45511457],
[0x1368913f8c81b29263e1,0x76b6dd44eccb1300085e,0x8f5c22ee300b1a9a89c0,0xe82a2c4e899dfec1b471,0x31cfcccf0683a6796925,0x13a8eaf5daf746d74fce,0x2b5935eff9f141c544df,0xaefea55d9e04b1bbf936,0xb0e9f6376a3f1d1d951a,0x7042943882d9dce9ec94,0xbdd46586b75743f2f4fa,0xb4721991e9f636bb8cd2,0x60de7311976dc5d06783,0x4ad05d6bde53e7f2ade3,0x4de0e1a18dd81c9127ba,0x916df37a52f0c293bcb2,0x54f61d973804fc6f049f,0x900a76ad6efeae74d470,0x9b0f58198535246c65fd,0x891314ac119479f5dd02,0x7ccd2095847461af2936,0x73a6764495d96816383d,0xc6be59c7ad7679af1667,0x7cdadf8676b75420b38c],
[0x791588cb7f592aeb0b4f,0x4357203410ad6044aca7,0x9dc6efa508955f69b483,0x862a3def1d6fcdbaf9ae,0x1029216231c2c9134135,0x600486e5e8fc78764a7c,0x5ced970952cd219425e2,0xa52384ccce5da27d16f5,0x869757bfbfdb444fbfac,0xc5b541f90c236b821534,0xeea268912d29757a26df,0x8bfb3c52346755813479,0xb25a07c61891fd0c9127,0xf51b1f40cf303619abbc,0x8008010036fdd1994eb8,0xac23a55d5331eec63301,0xeff1729c14b2d14f90f8,0x84beb5d8f88b28b1072,0x2d4defa62deb3278164c,0x180909283a0ef8edad8,0xdb5d45bb14ccb7064e9a,0xe01e782bd0b25bd7d44a,0xc4387a8aa0795e6e3354,0xf761668f6988ac01a73e],
[0x5ab6e6701c2148123261,0xce3a7be8068d20c76a8f,0xb389e6220cd7c63473c2,0xb2772c9943dc42f84d84,0x96fdf2b37aaa1e71423c,0x9976a544829dd450dcf1,0x8da4c52f9a40aa5a3d12,0xa7096e3fbdb30dc3d346,0xa352fd89550befe5787c,0xd2bd411c79e19102ed67,0xf98e8977172267a431c,0x8b88615b984bddbd4b8b,0x4bd56f6f6009ba8ca470,0x773d11cad8bc77b492bb,0x471275eef822931b10dd,0x8bc2fb3d63475bd31691,0x608b5935d5de0d6414c0,0xb15e35012a81dda13b61,0xd3f7cf684cdf3c12ac56,0xeb0ab9858fd955fc0d8b,0xfdeaa15bac0ff8d2a5ab,0xbca351053a8b81bafe36,0x11fd5d2678194e434624,0x81a22007cdba8122f72a],
[0x7e9aa191fd4b856a48,0xddfdd6aeeb6a8802917d,0x57227ce52561b8d45728,0x67a9332b4daaa21acfd7,0xc6dc7d93163a4bb75237,0x543564c05c341f42d6e3,0x1a78bf8fa66560ed0df5,0xa2960430b8243d599857,0xb1c7f5e343aa4dd70167,0xedfe8be0504b0cf9fb39,0xc9961ef1bd5113dc427d,0x12f73b5a132b36b70c3,0x4547d01df7cc29650b2,0x6ccbd5bab5b227cd6c47,0x8c83c1c03e3ea8aa6b9,0x14233afef8ccd8c1cae2,0x468e395aa446e03dce36,0xdfea9c92e481aab81fec,0x2cf99d1b0d967e4a6fdb,0x3ec1917d2f98a3a75230,0x5159714994b8f2c6a503,0x23413499d6a7f81a7428,0x2284e255e442ed627968,0xb85c7c1e82f0816f20b],
[0x73a460b0a2e58d8a48f9,0x1961aeae201c773f5df1,0x94c9b0658ce4f6801e86,0x550630376e8d62d43bd3,0xb4ebd500cc5c723023fc,0xea733c2b7d6c3e46896,0xc6cf2a68939d3f39ccfc,0xb3aef6dd1d20b559d146,0x76e67b111f4231c92f34,0x3ccd1571781e5a6634bb,0xf99b617449cafe57e7,0xc6f0b48d825d3d290e05,0xa538d6082ce05f15ceed,0xaa8521e6f8c8540a764b,0x8b0fbcd0959ea81de093,0xcef828e59c402b6e0a35,0x2ce5ade7532c2dc81672,0x495b48db87676b3d6b30,0xf8a3890a1cdaf72b5913,0x438755e370e11ac56c9b,0xa050570fe91186958f9f,0x1ef3dfff6577503a5309,0xa0e8b59ae692767a86ea,0x1d2ee410ec6b6bb4e90c],
[0xea5d20af639ee23116b2,0xf90a56459e906f359562,0xf396772dc18bcf1464bd,0x1c0b18eb31d3a5f3d6e7,0xadf5ba078049e56f010e,0xe0854895bf26c222d623,0x2d9b9024cff9b8f7d9f9,0x9cad63893536e42be8f5,0x5b4ac0574b52331655a8,0xf0b370dd7ff8bc7874a,0xb2e29d97a77a622af20d,0xafc366dd006e13422b1f,0x197a203bf117b4de3f1a,0x4e128688540777796c51,0xf4550ddd678ccaacfc34,0x14a6d76a59013453a4ea,0x1418e3053637b9c4c08e,0xd50bd429065444d11549,0xc489b5e15823ced363e6,0xeb5194df52c5ab4f14c5,0x2e1e67e824560505f5d5,0xd1feb8706b9f54cb0ff5,0x53617d4df87b84e17c63,0x6c32608dae5e564a5a9],
[0xda8c2c293eda4fc57a1d,0x8d64f9262430b690cd12,0x4b00414d2463583a4354,0xdb0a541108bb971050c1,0x623c3d07599e07f31303,0x301c0517b65fbbe7966c,0xece8172670a32c8548d,0xf515eaef5bf45159550f,0xe00b7d6ee0647cea4921,0xe5eef143b6c7721c89a1,0xf4c8d91f21190a7e8caf,0x63d439dee31f0fbea8f6,0xe117eb17fb1bad0b3f9e,0x9a2245997e9fdd816f34,0xb15ab32785145e023f99,0x9d8fc59422918be331a,0x3315ec56ab02b1c2e514,0x2c167ff69ea3dae392f9,0x6f2566025a2ebdbf6b1e,0x7502977ba8f37ce91fd5,0xaeee50b081e163f3ddb,0xc9ea4c3a465edb70704e,0x680297ec7e9fdcb2e7c6,0x393f40c1adabc667c344],
[0xe6f5d337c4f1d2b36607,0x62132eb80eb07c3cd9f7,0x132fe7bea183fd728e61,0x4323e5925eeff8e33464,0x4f8c71af97d9e60f911b,0x55a0779053fc43bc8b6e,0x7b1fe7f6fa3fed2950c1,0xb646a00cb9ad0c049955,0xcd568ae3f9599295e930,0x546a42ddde31455ebcf9,0xa8324a451a0511a95f73,0x2f3d454c397c51df41f5,0x3e656a947c974bd5590b,0x11fb15dd5fbc8779e7b8,0xe8070d763d078116209d,0x51a0040c83df4c71f6cf,0x8a82d6543cdc137820c3,0x8320ad8fe2e9d6eb0ea2,0x617a6c3957b1720f319d,0xcf73bc6baace6b0b174,0xd28e02332200af253217,0xd4a724286695065b1170,0x364f183a373d16faca9c,0x68a4190441cc92364c65],
[0x4b569e506f2ae1b55490,0x329cfea6c1c1e8ab16b7,0xc6a6fb2cb2f3dadbbde1,0xb813052ff250e3ddf9db,0x3e89b2ebca2ff75d69a1,0x226567553c4d6109404e,0x30bf8395f557c9ae289e,0x871aacb8185096effb8f,0x5af6ac81c197deec534d,0xefbdb2290537fab7622c,0x595a66c52b6f4b43e202,0x4d2cb1e44673db7b2e41,0xc90bc1e1f252bda06987,0x1e47e871cac5204dafb4,0x5636c25af5260d45ea85,0x62b6144c1b950fecfd78,0xfbdf9eeecb85be2d2eaf,0xf24458c9370c0209b10b,0xe60066f3377f8428fa1d,0x30de14abe7b191d4e61d,0xcdc4a8ef5be440590fb,0x681868a604dc2bcfe798,0x19e9c620a1b4ec47d023,0xc02de295a95ac9f66b45],
[0x571a2100c0d248aec05b,0xd3afdd9923991e6398e2,0x63b670a637728e49416d,0xd6a6568c1728dfb97ba0,0x9f7afa1f588fa12e0125,0x4e90122f1da4acbc2b84,0xb6cb2302aa34f1ee89e3,0xa281f9fae77fb0a2a65a,0x90f4175ec25b4039273b,0xe86a56a011d2cd65993d,0x9fbcee9c65350a70236e,0x863d7192d083c9514d0f,0xdf92ae264c56dccbbbdb,0x1983372896d1abd88fe6,0xd818a9cc08b1ebb394ef,0x84a96f2e14f32c4c932e,0xb4c2ddb91541b2990944,0x99b019be664a5a3f3504,0xf3c74d8b7ec2d374923d,0xa8cdf3a76c90f35dd58,0x458e10dd1ec3f05c8c3,0xaea38f3c40bfe60cb866,0xf4e30518e616caf55cf7,0x8ba68dcd3c72bc7c782b],
[0x1e2f640034681dd7c466,0x5ab1d8830e767a0478c9,0x51f945d0985b7e2cc4e7,0xb760c57aa8046c54f8c4,0x47e8405e00e05f284986,0x9ef08472a0af7eabd259,0x4db99e052c569831c3da,0xccc9615ad99072b85b3,0xbd4855d1583e8d94b541,0x14499ecfac196c9982ca,0xdc6e1bf7372e7ef1bcaa,0xe18bd362cf8cd3c4563c,0xd5dfd2b7d29fa0ae0467,0x4f5fbd4ba1f1602109ae,0x1bd49d36afd977056abb,0xaae7dd050658d4dbd452,0xfb3a107c247c92aa1f0d,0x14d2d2a18a3aaae1d12,0x539c562b8301810b50cb,0xbffa0566ee3aa0e38435,0x4f99989364a3a9b38689,0x1b4747abc61141b8f3c9,0xbf0214db8840b2011eb4,0xa7db69be4b1c7c1b01ce],
[0xc300c7389bc22cc3b171,0xbbadb1f9504f8fd48094,0x3e3b87f20965cf750342,0xeef2ef491246e13685de,0x13e4eedbc598943fafc8,0xd3fbeed6851faced97ab,0x825f47ef4bf3a1ff9d46,0xe84b7837b4bc4fe8de85,0xc3107cb964fb09de89f3,0xaf50496e217e43c34e35,0x85716157120c9c3fc7f,0x29284b2b657a7470d0b7,0xbd12a3c1dc2854c95747,0x71d17110021f067a422f,0x3b8d443d4fe299f872fd,0xb40a3edc177f83c4d58e,0x97b28f2235a9ec3fa5f2,0xb4d61a8699fc73a0d497,0xad5c5351ccb897601cbb,0x111df0e1af6b55b1481b,0x753d3b26252bd2d63246,0xae25e5237638113b5d5e,0xa2c81a04f1cd010ddd05,0x9285a62a168a091b7bea],
[0x8a896f58c68800ecc69c,0xdd0a30422fe3337e123f,0x7c7ec7a923092d30587b,0xd22fc5d767f9b5600fb6,0xff06c80884bc9533ca,0xa1aafda3e2dab1eefbbb,0x410a2f36d5ed5e7abcac,0x515605422237038b991e,0x8055b543faeaa676191d,0x99d5aa371ea20a7195bf,0xd26a39b535292126a894,0xc1b241ab09819d003dbc,0xe7bdf91bd7e84ea65fbd,0x558cff290126e656aa97,0xbb2d00c889f1b62752ba,0x138d0641ef9bcd9f33bf,0x1e1e8456939a5ddf1d1d,0x40543c0e55a135f9ad09,0x87af0713e64f3d72f393,0x9de48c152c6564dbfbe7,0xbca02e2babb11891406c,0xf41453028a049565c412,0xa67a6555d4ec49258758,0x2543a722875eb30f48e9]]

def tile22 : List (List Nat) :=
[[0x9c720a6f0856ff5c3343,0x11aeb49e1925da58c785,0x3f610a90521b8af30571,0x764a560c6a7db5097b74,0x35660f22fe47680a0e6,0xee1874e0060205e7698c,0x298656eaf96b52522c67,0x381ece9330b12ad251cb,0xdf76c4c4787d03c66dc4,0x915d5e123fcecf5b697c,0xdd4ccc97ee9170294209,0x55816d7a850eaafde504,0x18ddff09ed66fc066a35,0xcd3fb7ff029069e0c521,0x3e67b3241ec91a0271b7,0x6358e75f8cfa6c93536f,0x799321ebf3f5c8da5299,0x9083001833fefdb03b0a,0xf3a53e1f9a757fc37ced,0x8429b404c4dc934034d9,0x9bba1c796dc04f87bd9a,0x4f503a2a51db03785a6b,0x19c0db7803117f2a720a,0x9823953158e911c579f5],
[0xcb44ed7646ebc516c5c3,0x869cf4197dac31954d4b,0x30f78533cfdf1a253289,0x986cfbd70f3377ac7d23,0x69b11397518382047fbb,0x952825fc5f029ca9a34b,0xc24794100e5a7a98ae12,0xfcf6c0beacd62f4afa28,0x282b91c649335f365fc,0xc034aa700e4774d0fb9b,0xe28e61bc674e8272e299,0xf1b56f19bc1ebc802d01,0x6a0844d4726e9aeba536,0x32863cf24f9730bd981d,0xe9eaea98c820b4257a1f,0xa46657e67ab1ea6c1dcd,0xc7320f88ec2d1c976a00,0x37125c9d4e02b5cbd2fc,0x5ed7d6cbab97c7fb3f63,0x5d20e5c4d801a59883ea,0x302a16bd38dc8357679e,0x4a9563c3bf60315fdf83,0x8f6be315b3df9c26fa82,0xff0ec18d0fa02a17a111],
[0xe5b084d9ad89ba845929,0xc6180aaf16a54a7b63d0,0xa8b1b73e2265598c9e56,0x4b2c9a5b1535ea25c078,0x1f3f5a4eae4aee4a5f16,0xe48a0c478bb30ec44878,0xeaaa84f01c6e50360f97,0x28e627c4da52caa5d000,0xb6d5943f7b6d2d327568,0xca900e42a75bb1b24a38,0xff9c4c3e8d3085526094,0xcf502277c48f3eccd30c,0x705f956b1f00ebc73d8,0x9150cb101e6fa25f79b5,0xa1aba4ee830b3a0ad20d,0x31271db76b2989ee3c13,0x68c4252cdff5240373bd,0x109b90f01e879cc142c8,0xd93ec00991b161a5830a,0xf34b0ef36096d4c4bdbc,0xeb734e378c575da7cc84,0xb1d1b2ecad66618ca7b6,0x5568ba16b547690059a0,0xf24706cf1b878346d8b4],
[0xa0116ee3c23b4142d38b,0x79408e4d475db216fa5,0xb3fd83255995ee06c4be,0x4b424f94342fdbc321ec,0x3853be7e733d4610af14,0x1d84805999716b340a6c,0x6bdf4c77ecabdc820a2e,0xa33a543e7d2b2504b729,0x3b9351bacf1ee53eb6f0,0xe973e94fb59686425e8b,0xcd9a0c64775e6a5108c4,0x3037a1982f60ec1cb88a,0x702cf87deaeffa8d6a02,0xac8fd9fe957ef3c8ac2a,0x6ab22416081add4526a6,0x1eedc42b90f902c5937e,0xb1cdab21590bf9c34e4d,0xa91320bcb016f274d786,0xc60cf37d9f1351f062a1,0xc3884860c2ce2fbcb240,0xd3b638bf612c706cd34e,0xa77013ab3da12a6bc96a,0xc537e177e82c7802fa46,0xb9cb819f4571542f47be],
[0xd6d41fdd3fc528d8648d,0xfd26de9fc33dcaa1ff6b,0xe7656d7869a6bacb10c9,0xf3e1613f3a44a25f116a,0xa2ce87011a91dbcf71dd,0xa7037321c649fa824fa7,0xa5bd24c6f470cdc92493,0x42746a0bef5b2ad0d1e7,0x9d1fe832e5c8ce86f180,0x870f81eafbd72e5d7a8f,0xb5712bedbb775753a9c,0x480dadfa85653f32c158,0x40497cf35e8e1d1acc6a,0xea0e53ffc0e60d12849a,0x33b3ccd1f5387f390d7e,0xe4c76f532acef2778d2b,0x63be00a2b558f51ed43e,0x7d4f2348a3df9ec6d3f3,0x51daddd1989020bbb6ec,0xcf156b8d0bfd3eb1d100,0x9f329220e94db50a4c19,0x4bb1dd6ce1c03cd0d35a,0x8fb0c726fa7ece7f7065,0xa89f9bf9b9e1b9d2c35c],
[0xc0465dcd40a937a28501,0xdc72286b6aa74c26041e,0x4a267f75acd0bb7f1ffc,0x13852036327c36d29136,0x5193e769e5edfe0582a3,0x1c315c04c85259c0e04a,0x8ea6bf25342310ba5037,0x39cf7165422d539b169d,0x8e7944e8187786503ee7,0xbc5b9fbaa1bca34116be,0x981c77bb56318e1cc416,0x9f865bb3edc5e0d6471c,0xf33d3f8eb08086feae34,0x14b35bec492d2facc398,0x378934e12bc00aa804b9,0x3d9561a98e0717ae7c8d,0xac14f3fd666f01a643f,0xb7123f4fcae1bfbcb154,0xc7a13a32f3ba721baf69,0xa3d5c4bf4f2d9f7057c,0x8155806dabde4cf1c472,0xbca3797ca44e8d038b10,0x42ddf48f03727c319e75,0x9d9169efc684428e0a36],
[0x6e32f973b400d1e9ab67,0x8064d660207bc55f883f,0x61494c35ab97fa77f4e2,0x1004e54a876fa3af1955,0xb8ce2733a1920c8adfe,0xf4299f678b28aee39844,0x4fcadd4a89bc52b6569d,0xf643b3ca6f8e314eacfd,0x67f6a58cf33da43bd030,0xf37dab1a14b6dacbb36,0x1c8db209607f3a0e1cb5,0x40fc1068f8011b894d63,0x671de0639a47c115e824,0x6b51ad4277da762941aa,0x9b852b8ab996b483e60d,0xedfbbb95a3715c8f5928,0x39e6c52cbac683c38c0b,0xa09c2550ff4ef2585e05,0x70a047e8f7878a80de28,0x7bd305a32da4d12da43f,0x1deedc4450dd7715b67,0xca703bdc1f92677ec236,0x2484b7d48adf65f0e3f1,0xd7ce72f5ecc04ea542ba],
[0xc0ca4e2b98a4dd830576,0x38a63047c783ea41c383,0x1f22eade8be9c8e4f89d,0x477a163fe8231f80e9f8,0xbf83834e28bd9b5b462b,0x1372ee2a37a45a56551d,0x2968eaa1898745a1bda7,0x5ed8cf093411eedd8eba,0x4eee087abbab5ddec980,0x81cae8febd69e18125cd,0x624fbae71876aa977cfe,0xb3d200bc027d2047e765,0x50f7c6bb578cc2964864,0x67dd9df87019df76026d,0x91769d9c5628ee14b84,0x1af4abb06c0cfa735a8b,0xab44e33a042b46db4d7,0x9517d2fe1bf003c71c2e,0x1ae5f513ee274e9c741d,0xd67ab078175e52ccc023,0xce9d81d08932edb0a103,0x4a1071136fc24700c7b6,0x97a4709c3086d6060716,0x1cecb51fcac9def0e4a4],
[0x266ae329eedcf275fc1b,0x5a7fd84237888067e916,0xfe1673bf20f6280b370c,0x3e2a7ad83c633769cfc2,0x91de87699d3361dbd770,0x1f1ca87fe293c6dc2ef3,0x1570a5c8c95d01bf83c6,0x5766d40493bbfd58e372,0xd787e8d254af74db8c4d,0xe5851259f5f705197fc5,0x24ece6301087bb5076c3,0x3965250771854f57f9a6,0x95236cea07ebaf253a16,0xc1c461e381fb50ab1e79,0xa5d29fd321d40bc5bfda,0xda7a17681606b4c77e80,0xe761e57151cd41392c25,0x28ddffc33bbe972b8d7e,0x81cf93698e74a95e2e48,0xccf9e166a0e4caad0921,0x17118c7fb33a6b721dd8,0x82895f929d8ce0c6f5a3,0x715625923a171768e915,0xf3e74b956d13a8109f3d],
[0x49cb35646b14f16d320,0x135e64d81ce4f1ada2c8,0x70f03350b1747a0c3b24,0x80f36597142ac2bbc073,0xe0f9dcd3a0f14c2875bd,0xa01cbf3514e31147feb4,0x768cbf8b9fdf53aad731,0x69708b07831f74c160a1,0xc0a579ca2c641e73eaec,0xa270a29481397c1fafa0,0x58f1e32e93aefcdbe484,0xf3fc3737730f169a0641,0xf2c419cef2c32172ee79,0xe70434643354e2c9e74b,0x36e15db1d366a6797e58,0xfa5370d997bc9cef0380,0x177cb61d75065b08d650,0x50c15a0351a863623a2b,0x20f3b2758f0c43c46168,0x55ed5244e98f550ed39f,0x4cd70cca0284435d7356,0x522ee9a31db980e9192d,0x8dd77d829e69c906f82,0x30dc40a11fbe8429b79e],
[0xf2a5a02b02d1eeaafa70,0x8c011890e894256d7828,0x24c69675177528490d86,0x1b1466b6697e5660a744,0x69e4e2ed904be6ea79a5,0x5dadbaf7044ce9670ce3,0x43fafd0b61fda8cc4048,0xe6808e555b3cd135627e,0x3494e0650cafd429d4b9,0x5a3880946bcfc3e10ed9,0x7816edef146e99b32d66,0x7a9c78dcfcca8969b1c7,0x4f38f5ba285a61ff0c6c,0x146f96c25400996a1f58,0x81dd1a883b5e3d051789,0x2110deb4381bfd8df2ca,0x86153c653c42a7459b0c,0x9902581e03048117960c,0xedc1e26a871f262d3d40,0xd82abb2bd4bf53e1af80,0x294b43ad56024624b907,0x20ac968f8f4108554fd6,0x990ffdc23ba558036199,0xc62355e8a56862e8e29b],
[0x2205bb504bc04867231d,0x61888853ec104f2f6ad,0xf985e1bd2541af31e593,0xcc94713fe124e74defc9,0xbb9a9118e00e70f5ddf9,0xe696544b58071c98fd5c,0xaec7b3d6880c47776cb5,0x5f675e7def57ae33ef78,0x8398aa002a66b372781,0x442243519df5223c9fc0,0x4db22c9aa25b10c4a2d3,0x6c6c07ee755bf7542a83,0x11fe66f9619ee0165e7d,0x84afe04fa9ff68a74b9d,0x199a30d2375a60e36b56,0xa7520a50af1f517248a7,0x3370b277a60999a56e68,0x58940957c38758ea717f,0x1f6c9b3b2e0bb9063f12,0x98f128facfd78d8dd7af,0xbf058b8b509a9f3d00a0,0x1c00871a2e3ac8200755,0x137e8739cf98ec8813a5,0xe553f6796bc12ef28b6a],
[0x699d3c3114354115d7e,0x72feb946475901961929,0x60841c3ac82007d2cbf5,0xa4fd33682e41f640ce16,0x82e716419b15148e114b,0xb6109ec5d1174cd0dab5,0xf57c3c6b5a0e97c2871a,0x1a01453d50eb8ecff5fb,0xf6950a1df10a4e3e5cee,0x2f7230187ca3c698ebf4,0x28370daeb905bdfda0be,0x16efd80fcf33550694e2,0x11169183dc790e98a2fa,0xcef624a10b4a3837f463,0xf180ad8a4133e2a7b557,0x146eb14eec297b4f323b,0x1584b3ccecdac72e73a4,0xaf0829b04e0ccccf6ed,0x45d36a0fdecdebeae529,0xda878bd1a749ffb6e91a,0x60a5382b6b4ed55fa766,0x41db96179305c7cc71a1,0xd0604e07edc53bbae826,0x869ff790dd9306e739b9],
[0xb938f96fabdf49ba5c56,0x3785f8405b773ed1c8d8,0x11fc322ba565bb3b0091,0xa0913fade95f00ec7bd2,0x341ce1e00305a9dcde5a,0x107ce0e6757c67605a44,0xe8b9b267d4eaa2fd0e29,0x2856e2294756eba6b2fe,0x1083c774c4b0c6a08a8e,0x7ba4e3c199fee8d77b97,0x4760b4f3b846ddb23dde,0xb243e466d2dc704e7875,0xad28a4ddf55d9b69dea,0x59fe5e1faba21dcef277,0x96048bdfda562091de41,0x6258f7617edd5cf408ce,0xb2452a6b94216e7d29e5,0xc5b0d0ee78c9dbffc071,0x5e1adff948c60be6ba42,0x573a5d758517b9651231,0xf604692e9581e627fee9,0x231d9cd1a76c41b5aa80,0x81f9f0e259e6d43b2e,0x181030eb784b2f7bc907],
[0x3d216d2367a3eaef8127,0xbccd4cbee4057174,0x4c3479198d398d6b93e3,0xb657e163b8a1bafb77ab,0x1320ad9cf52328403958,0x532b2514c9fdbf308a2,0xf3b64834a1bf91761783,0x4158b1ec590fee9e4e9c,0xd6a2d8722dcae6875707,0x16a1b3ba9c5b8a74ab36,0x8a58e7d1700d1487f36e,0x514d004e0a570698370c,0x19c1948b1969179c3814,0xf1cd8abcbae8ff6d01d8,0xa4788acbd300accb658c,0x1c8ab4868e565c4f1e21,0xfe353177082feb94f60c,0xfe0e2c9b193e50a6bb7c,0xdfce169ee7d2521698c8,0x1fa9b21aca708b65a34b,0x7e32808d9118cb2cdd85,0xf20afdd34fc8d50685b7,0x437d8c03b48a03cb51f3,0xad7666fff6afebb066bc],
[0xfc1d4e0c03acaac1bb6a,0x6070baf2abe85e6de2dd,0x24f5eada287ea8feac41,0x796a85a26df774b3af1b,0x8960744dbb1e11c0562e,0xa2a740a34b21c6363af0,0xbee78c19b4210ac02e52,0xa9bba29377da98039ba4,0x6e8478695cefb3a01457,0xb750b06c0fcc6f1f3209,0x2c5cdca70c9c1323651c,0x9dde030362b31414b245,0x8040e312aaacd4175eb4,0x1c7b3515a367787fe2a2,0xe956c006bec34101e8ff,0x3ecac26eb1111e239f82,0x2d6b92520c3dfd30a2cb,0x63fa6b8900b678818de0,0x27a2bed20b63d2ca3419,0x7ce5f2d80e133150e4f7,0x3a73eafd5e3c5e28994a,0xf006f3d6d404519fdbd2,0xc1552287eeba8e05b6,0xbd3d05e9be7bd769981c]]

def tile23 : List (List Nat) :=
[[0x4f60c5ad7a7e03f41200,0x189b0190dc9198bae0ec,0xdc5b41634d97c74c01fb,0x5ec4144e69d4b0b34a3c,0x92355deaf798c02eb506,0x9b330c9eba6e8d970ec6,0x459eeb4ff1463ad9d9be,0x62f2a3e807913b8d814e,0xcaa1c841fdf3e4c5e400,0xc3ecc914fd8e8d00dd80,0x5f221fb09978035ad968,0x41d9ac0754dac6dd8ae6,0x837ee878812d47a7510d,0x2665bcb57bc8cdff340,0x8e28fe724aa65b7f7566,0x89932783f15f843c96bf,0xb5974053e61a8bc41031,0x59d64d7652e99252f902,0xb1989a52eeb35ab71eec,0x756eb2ff31849ed7ff76,0x16457d97620727ddca02,0x40c892fc2bac2973abd7,0xd870413941122b2bbfab,0x836305d3dacdaf49867],
[0x1a87030825b2569efb46,0x335898385feaf7d32b75,0x2889b363afaadf11bcdd,0x754b6c37e6acf0819193,0xe417b823b52908474c20,0x616ad3af9df9c0b2bb4,0x53d5cb95c3a54787197f,0x93847a71ee20538a886,0xeb64f47070a8ef9c6a05,0x4385ffd7ffb7a85e63bd,0xfd2dd25898cf03c1667f,0xfae9e2ba9fb91dbfde78,0xff0a70a6a7322a793107,0xb59dbd45f4491fe1f32c,0x80906af438c9e8a5f551,0xc6e423cc37fa79515ce8,0x8bbc0f5688b43e246895,0x3653a2ac587f8386f8b,0x750047ef9568ed4036da,0xd937c4bf1d4040ef6b17,0xd284ba01783a5ca007e0,0x6d17d0d831e19d76b079,0x1472b25859009de4a900,0xd10332d1ae9b7839a814],
[0x1592b5fbd0f7b0a7a513,0xfc35398c32793f629714,0xe1c3e44fc964275dcd8d,0xc468731c42ca7ab23f52,0x8f7c29fbff7be16731c2,0x61c3ceb51d05e78cbf72,0x70edd8235ad7fc1e00ec,0x366c51b3933217218438,0x25a490a5fca841d64129,0xfbacafe7716e58f6dd2e,0xd163a7d6e784d4baae21,0xb5e451d5a40e3621efb6,0x35c3bbbe501a39d7c36c,0xe643e7dee430bc5b3b4a,0xeb7922a04676cd5ee07,0x5f5cbad72a721b68e42a,0xbab01c358abfb987b8da,0x1ea77bb2dba65c7c81d9,0x755ceb893bf809378d03,0x48d8a2cd834fc62a5f5d,0xd9bf098124a33f5edbb3,0xf6268594fcfef303aaba,0x3fd1159e7beff89c728c,0x85023af14781c9df78fc],
[0x828a66818385c9bb68d0,0xcf6fea9e851e07e020d,0xa13a96890cc07b1abc84,0xb399f11d0f84c4b5f5d5,0xd7dbc8175c0605f46f94,0x2f4d059009eeaf20d722,0xf85fbd1cc11cca9072d8,0x3c03ebe3fd149be20423,0x9beb1c423f568929d494,0x1bd6afcfa873f15d0f90,0xd4034e3172ecd32ac2ce,0xd752e169a4a1e77d75d1,0x719399dabbb4763b9f94,0x13444695604482e53b39,0xabc529e1ea9c30337426,0x321a8b367306854261a5,0x8891fff7931f797d1670,0xa81a96600b39ee82c862,0xf2690c96a547b22d8ef7,0xf21cd5d351386c129dc1,0x7fb0e41e58e18300ab26,0xc6f21cebbff91c6c50b3,0xc966b778297416eeac84,0x6837637340ece1c2504f],
[0x97366898fa054d05d7a6,0x87cd78b1151a35ab9969,0xdc8d75d285a4bf57232f,0x354ed4aa0112a1a915ff,0x45592328bad1c3fcafc4,0xae7274c320bbd02b1f1a,0xb58e4cae1fbf57e930ef,0x7aed07dcfe2db41d0cf4,0xce906b423c0fe471371e,0x9a1513527724cc1fce5a,0xc64decac4b2cc236da1,0x7b25db0f8c82e359e84,0x7d34947d682c01b5ae3c,0x53a7ce1d9644ef32df41,0x655547347085fc490121,0xaf277480a36d68b6c635,0x487337a6826e342a8993,0xca85d9d8f5053e321897,0x53ddf85d87d3ee77abdd,0xdc289c8a21badf62cd50,0x9f25851c6d36b52be31f,0x53dd7e94bf6cb179fda4,0x8cc1bb8096b4e7295cde,0xce6400ae67e5db8d4182],
[0x5b1cc07dda6f5c06fb7d,0xe1502dc8714efc1bf279,0x65020ee48bfae093be00,0xc409ec3b8024db0ea0a8,0x79ffc901264bba915a74,0xa7ce1d9644ef32c398df,0x778465cce0914e288298,0x9d89283c7f8b04a7fda7,0x76d773fc9b907d47a63d,0xe9b448e778bf61969e9b,0x2163b7624d25d0a2c3ca,0x1c8a5e62af333f364569,0x5bf12af99293b31fe128,0xef735edeb82b5e9f8dc5,0xecc0af5029a92840f8e8,0x5efc796867d0c3b2478d,0xf969d00f9e5e621d7837,0x530782078882c07b7b4a,0x532141de800a9c64bb3d,0x8e0fac132971af51bf02,0x1cbc43a817c5f2cc6fcd,0x2505d75879db084cb75e,0x6e50a6654ce560da7f2b,0xfbb049143b0d4415f01c],
[0x74879ef61dee0d77b4d9,0xe14a5b91167067e87fee,0xb7ff82d73709bad6414f,0xedb866df7bf9405470e6,0x241332e5f077c085b0fe,0x9bc88a1026c9057ee534,0x300a1f4b0669b5f2d5ec,0x5716189e284834e933ca,0x376ff1d1348e1ed2ae52,0x4df84478b5cd8121e044,0x5e0435aaab34e960289f,0xa57cb706e3ab89cc9f0e,0xdd6125259b16e79dbee1,0x93ac064cb221e512aa28,0x903f7628c3569eaf3484,0x60e80c39eba129770477,0xb60fb3f4ca2263b211e1,0xe9fbe57717ffb17c1f8c,0xf2701101bc33a96c8baa,0x34897ebddbb45044936c,0x19a00ce07cbeda635654,0x2e6b0cd1e5cbe60f2e87,0x38b058a0e2968bcf35af,0x7c40eac635d8d9e3305],
[0x4d1d273496fc68ebe9f0,0x7cda3b7a05b3b2d28907,0xfa5f1e55facbfe347a42,0x112a3d64935ac5b5b514,0x97cb895f8212b3377615,0x14dfab78825483038370,0x66ee839048ff66ab5628,0x7fc2b9cacf7bffb4786c,0x261c896fec94ad504edc,0xd474985e0e71f2e13eb0,0xb269c22b92d89db17b74,0xd2c3aa3775c4c9dcd693,0xbe737cbc1b0d7b53068f,0x52b24cc4b31b6422c7b3,0x74f1c776debd3f4280ee,0xb50eb1a599c55a189d1d,0x1d6ce82510f2fcc48ff6,0x4430c0ff48f87464d1de,0x903bbd1f71aeaa5da85f,0xe85ffdc740ca6e5f9902,0xe64c271e8f931b4fa1a2,0xf280bfe3274577a518b,0x77eb9aea01c59699137c,0xe7496198b42b200ee085],
[0xce60b57ddea668e5c537,0x6100ca5b7d6dbfb79fa8,0x16b1fe1763758be0b9ec,0x11095a7dca1a9fbcb993,0xc64c835d2008b9e73970,0xdc180c850b3c6981c32f,0xd2b7dbd0047754c573bd,0x2f1d29d514be25fbf162,0xe7c8e18ff2b7ab80481f,0x125429c51f5b81277bcc,0x830d2bb9bb8ac3a4ac5,0x130114147e2cf8aa34fe,0xd58c9725fa3930c58c36,0x9bf50cfb37d4cc59299c,0x31cf42782fe961b86725,0x6a87807f5ce3f4d12c93,0x7b16b74dfcf407f42cda,0x745e0693c0b1aaf2b681,0x6097a1ea89af8eac8539,0x8d69e7662a236d0820f9,0xbab757cbc1cc535bf81b,0xef9b83b3757e28c13e09,0x7ff703f7fea079881849,0x3eeb8c600a69d13aa7df],
[0x7de9a3d2eec3a0c8b4d7,0xf628936ff69b458d4f89,0x2f4b71c7d450254d9420,0x453ab8c920d8e79cd2b0,0x1db175ce4ea7f6b0f5d3,0xe05b316d1724845c51a7,0x7af3a4d1bc61bfaaf535,0xe117a2bc0b67cefb3f38,0x6c5504cbf5e73754358b,0x2b80f7832a183e2eb1c1,0x1785bb5c9d53941a2222,0xc24962eac10321b49d1b,0x5c55ef4cc8138d82fdf0,0xbdb483246b830b5dc2c,0x3b64243338c61715830d,0x4eb9307f127a11aed52b,0x2ed13629824a9e312e6e,0x2185ad20646fed9d3fea,0x6c7b96290a44b769cbed,0x9c041352aa136f702939,0x93216b4b8651d0d64bb9,0xad759d497d964e55a054,0x739633be57d64fb698f9,0xc770c103824c08ae97bf],
[0xb6d7baf99a25415bbe40,0x4dc59e39ee303764c00f,0x3f1cfa5e7c41386affed,0x3e7e18db22139002ba26,0x6a17ee4a5a7e2492789b,0xc715c4027c55e12bc000,0xc6f68f1105813923294e,0xdb7aa2a8aae2a002cfef,0x16680c8b19061fe3ad3e,0x7d27a4adf7ad77747e9b,0xe592bed8e9077dfd20,0x425b65aa4a82ac5d33ea,0x98062e7c5dbf7329909,0x5385005d1d9ab2b3e44e,0x1b5bcdda7cc378c51a24,0xfe9f481fdba5271add8,0xe2939467b0c39e346587,0xa9bdc62b2c0f3e446324,0x9d14c68365d4aed48530,0x688210d6408b5fe9eff0,0x640c4571b2e8a8ebc73b,0xb335748ace46a80a3e13,0x6d8696cc6e3267793425,0x611ea1fb98f16d837e94],
[0x960e1a6aa2c2b1ce2c26,0x56673f24ac0d957c34d6,0x5055200760a77bc10a07,0x9367da15d0b6b6784591,0xf0636ac212951cc1ba48,0xde297e3d3626fa0a7faa,0x794dd57830d486231a86,0x11fcf2494edc03e1b3a0,0x8ed0f4734b6e9b70c09a,0xe1be1e89a28988440018,0x5cbd830e9ed91146432b,0x42e72aac475e15105788,0xb9a541140eb20b28925a,0xd0f9907c23241a80058e,0x71beb1f85e33f37c826,0xcfa81a1f38b89f00d293,0xcb502d63770a1735906d,0xf625f4b16b96fd6654a7,0xb71b5489c3f81314bc48,0x2e3362946dd55032ed2,0x211dc5ccff5a0e92df90,0xb35580204df203266f89,0xeadc4813ab11049090c4,0x1d4eeff41b8b16e96312],
[0xa63ccc06548aedcfffde,0x4470fa91f7be612003e9,0xebd61827a4f3f8adbe97,0x209e8cd698c2001be62f,0xee421d7f08176e34e9e7,0x6eb974f3fd2fc0025bee,0x6dba77077e3b77f77e02,0x85ff80340ff90eecd3ce,0x979a8b388d00b4c70edc,0xa107c4ae41886c81b95c,0x8e2749bf00f1054d7260,0xd317e09a0b55a078e96,0xa6c6c0f07d02672e12db,0xad876e63bef921f53d42,0x8b6ae748c7045306e774,0x76348125b33d1f0ab087,0x95dbe89d8f468e7d8b1b,0x3cb3c3b728bdecce36fe,0x20203cfa930c88404c53,0x3a15088ef0674aeb9d99,0x9d8276a88b8eb011ecb7,0x41d79b8cebd576e91392,0x189b1d31658a6743b19e,0x4f524581195189531a77],
[0x31889eda6a835985925d,0x8678ab0144fe732edb71,0x9ed25be2c4512d1af95,0x3dc59f7ab0cb1fe378c,0x3c2918f7ea883d933cc7,0xea90db8c42c553adc1f2,0x2543ce5fdd44fe89b763,0x84ff1a74763ca0c06ae9,0xe958828ee73f036dc153,0x784f8ebbba14b080b8b3,0x9b7cddc5e37b28ebc55d,0x339f9d0cad9a65ce2918,0x154faf872eabbc5c9d7b,0x71c085604352ad8604e3,0xc0a8ad77f7be91bd041c,0x806dbd6f545a310e94d4,0xedc85039a33fe512aa31,0x4bc961378028060777c1,0x603758089ef02f2ed9e6,0xf21c7ead0c71751524b6,0xb886eb7f839e2721fd1d,0xce97f8dcbc0895c87708,0x94440235d9a89efef83c,0xe47062bb29ea04554a87],
[0x87da9f600bc4f5748545,0x4d9ae7615f7d96e618a4,0x820e119c365c567dd8f,0x9cbb641743613c5829cc,0x7bcbd77b1e68d2ed282d,0x6e59f4f0943dfa3336f2,0xa6c9d7995f3f03fd40bd,0xeca01e7dfa63c051149d,0x70a3804b005ef105537d,0x103d3a82e06d1de95088,0x364ddffcd54a8cda1c52,0x4c3063caa498c04a6ab2,0x3ad9b762e7104123d52b,0x63f3d98cdba188efbc27,0x33949f2d611aaa4fa684,0x8fa7c19e5709b0842439,0x8ed1151336c9853c580d,0x50457461470b0356b3d2,0xba95f9c5d979048a9d8f,0x95bb33dac58d6314fc22,0x49de4623dcd2c365e7a1,0xbd31ec70273e6a1e7af1,0xdafbb40a28e96bf6f1ac,0xc43164c68960f05cc515],
[0x1aa1a4513eb27523e2f2,0x18500ba54ded4345b807,0xec88f76ce57f58c51178,0x888644f01a0adcd97d25,0xd6f305e57e847a4b7e94,0xbf2fbfe0328b6e412705,0x92a96aab7b3fb3150454,0xe19a62a45af1eae83fa1,0x3ff8685ea76fa55bc7d5,0xeb427dcf2e0ff4fddd48,0x846febd4473ea3cfe320,0x1de6ed7de4492c5d528d,0x5fd4afca69b47a29db48,0x27a0823605b6a89a3ba0,0x36f124f8aab426723190,0x456698d859fbb6d3d5a1,0xa9b8b27b3fba7d218ed0,0xd02fadab5d73eaae3dbb,0x335bd9031be49b69bf53,0x69ff17c47b1507dad4c3,0xe39a0fe59858e28c40e7,0xae2a63c4cd10fffccd23,0xe32dc4f34175581cf908,0xd9b00f122c1b42f14b8b]]

def tile24 : List (List Nat) :=
[[0x318a59d91bf1bdf903ce,0x2c35caaa3cc990a03ce8,0x37d940594f2b49740855,0xd85fcae0894dda585c72,0x672bd50ddcae20f2a3d2,0x8e13180e713138e3eb97,0xfc86fb35dd62f2719c3a,0x189fc1f099acfdf10ebf,0xd63cf8b3e3d24b2fe2ec,0x9d7fdacd124a789015c,0x7db7e35cb5ef54ca0a67,0x6ab85d4f5cfdb92e2f9d,0xd394d28a9906075b6a3a,0x22ad3c5510d5fc2df231,0x23804fe18e7b39a007f,0xc2915b26eb31b01832ec,0x990975fcd476d9a45c6,0x9ae56daa6a5703f79f09,0x8c6e60138ddeab73ea40,0x62151ea33bbd9e80c7b,0xc1147426ef8fd9a0c3ec,0xcbe9bde384423a67089a,0x2a831381a87eff44db13,0x10b84267f2086cc93f5f],
[0xb6692ddcc11922775af,0x6558c92d83d8df5c9190,0x3432f11e9b72dc04dc9,0xf710da89b5235791ff00,0x36598d61ecf8c7f625d4,0x3dfe1f27d0dd2a815fd1,0xc018b5105e263b4e6c3d,0x4b38c003c4e079cf403f,0x5a9e0066e24f8f923e32,0x91a1dc1c5e83250927b2,0xa3aed58c8c38c335d286,0xd9dda01fb2990c69a3bb,0x22a7eaefa68944666907,0x7e50c0928f7095da579f,0xc2fb5133571e4209ed1b,0xf81e3a746045ca236fd1,0xa8f269210860ba77850b,0x960cf0881fc1d1f77feb,0x998ea3dc9d1ba5287f5c,0xb73f8618c2aacd478e13,0xdf73af78bb5d5477cc82,0x21e9cc1c4f3c0c54fd7a,0xab06d570a0651c3d4b09,0x7de4e49c9801b3cfd4ed],
[0x634fd8f093bea1f1797a,0x4f20f51383befebc0d02,0xd47db091d968cb269d98,0x6cdba29818127b60414b,0x39488a09f45fe83fb7cb,0x2fd94fe41c07ac8d21fd,0x13431ada9fea3cb8b715,0xa8438d4314411a7a638a,0xafdb406e17f38f6effee,0xe013d297fdfd966aa2f5,0xe479ad90c3c02f895e74,0x98f78d540ee06c5dbe5,0x6aa39a6c78a800ebfff,0xd71a638c019f89d30f53,0x4215e0de92cf041cc5b3,0xc7463fd5212e63fb2f23,0x6e643746e648e9b9f7dd,0xf3019c330f5ce9ea2ed9,0x3a9642d65271d99b3374,0x570d80c56134f9cebda7,0xb4dabc77d7c9bb391f88,0xa8fceba3f2b82cb2356b,0x5120632da68660777b7e,0x793294c73b302a47cdb6],
[0x7effcd0721e7dd7591b0,0xe02fa314c8ab2a8534df,0x8088687416a482e84dc1,0x48e1f6807cd88423d055,0x9bce6b66c8818b51cae7,0x8dd5c5b6c862165f34be,0xcc1dbfbfcebaab37cc60,0xd7495d5524cbbe87966,0xe3268c2726089b3532de,0xad0b113c11d078a1c188,0xf5a10a4189bbc052a10e,0x76fde746b377bf4648a1,0x78a3ab55d030bc432e96,0x3b817ed47fe5a031543e,0xd82604c67b3de70da5dc,0xee3128fcf6490c1be18c,0x42dac47dae1191cf1c87,0xe3ee2d3ae414c7008564,0xea7d6e12d75f8ffcd226,0x5850111c223947d98aa3,0xce9b3c38ccd3eefc871e,0x295131362a555d80c1d5,0x8cfd1a251a57c76cf09,0xf50d0e85497f27ee39ac],
[0x43aebf3ff821b3602b31,0x13618d237694ca57829b,0x7b794edcc421f4b6b7ba,0xd76a9b419839d90b5cc7,0x2901224a23bd67f9d8c0,0x67c263fb7f9d19fee626,0x5832bd20320ab3b24700,0xa9ad24b1585494e7e00a,0x41cb5ec024815d430880,0x3d7ed3bc613f54583b1b,0xf3feb323f24e8943ba1c,0x10ee532a696aa14b4b04,0xec75e01a18121799ea4,0xda82e8b275d8b1045752,0x249a87927ea0c499666f,0x79e9967142efc003e92,0x371f6c41ef4527942bcd,0xeeccb2f2411968977c3d,0x8a9959908f2f7b22e486,0x2e94c970d78a98915a3a,0xb30a27ec71731e0002a4,0x5e4dd1f4c320f6e4cb17,0xd13fc35178533226788d,0x7cc5efbb901489c623fb],
[0x369d90159c7fe5483f41,0x9f69e07090d29ca609e7,0x16515154eb89c934f01a,0x96aa84f977b2ab212389,0xe676d7961e4f95f6e7a,0xcde58f38d6cb817cd91e,0xf084437c1b3b8a33a535,0x5d9bfeb68dc6dd6d1728,0xa28193d83a137a24a5dd,0xa8c9fe68a638b8c8875f,0x655c0781238cdb23f504,0xe8b400d9b63a9c4cf6bd,0xb4c9ff136c864db32a2,0xa30e78b1c3eada1da99f,0x5f322a9e9c67ab827a07,0xf003c0c69ce143cbad74,0x2e88675a491639c36c93,0x8659667f3a8f77165904,0x357da005b7bacef85d7a,0xa23a370b4ef274b45b78,0x9c2d43bdb863cc6b1f4c,0xda7bc8b2b80f8274068b,0x95af3fdc0dd084e192e3,0xe4c7df10a5f37c811373],
[0xe0587d808a1904c27982,0x3837f5a8d59bc371db88,0xbe3d2607f35ee3b50a8,0x92299601889937931285,0x5a45ef64f1798b0c2581,0x9b7ef950dc46b1a95eb8,0x13be8f88aa6b9d29a309,0xf709f814a1fa06e54ece,0xc1bca726fd28d308630e,0x1408a272905b7e3fdf37,0x633032d51d33cb7877ce,0x840c3057101fe4e2ab66,0x2118f1b2411197dff9d0,0x988f48d626f1f3edc741,0x9c4d4d68060cf6ca6870,0xbcd90d00a1332434cd2e,0x541392f60907defa87a3,0x493ad4ef3d053d048d10,0xcaf75bfaa749f4094fb,0x131859a11f841dbf2a52,0x2d2452bb298d545ef805,0x9b4fdbd20527ced35d71,0xe6aac0f19f5508b85257,0xcfade2dd45be90cf413],
[0xdf185dfd6e5d7682187e,0xb403d22303fd3bad9d15,0x928ed267773b27708145,0x3295af103e30eb17eea,0x31f2c256ad4d4f062cc7,0xfdb4563f98038c5cc294,0x7af19d8289cd9592890,0x53fda577461a32a11aea,0x59f3fa991fdd8f13bac8,0x3caa9babac6470f74257,0x3085657cf2ba5047b83,0x9ff3e26e91fa04deb185,0xd96550deef0675af461d,0x7501197b129dba65819d,0xc45fe40195b04f33f24e,0xb6e07687a991184b02b5,0xb2eea658dd5d658276c7,0x38855d9a0ab886227eb0,0xf7ceddea93cd69b92f9d,0xab356e9f6c5cf767163d,0x53868dd3fc2bb86a1409,0x1260b4ed0700a0c19115,0xf75c45d44d56fce15a2,0x28eddf182b253b7eded8],
[0x1244d612c446a6a3f11a,0x3bd21a8f350da33d307f,0x24eb9ff2a402583c66e7,0xe41ae6fba34d8cc50a6e,0x1845583f08448c615506,0xa599fa92e1066bfe332f,0x25a5750e8df18f3751fe,0x67e57869252009ca5079,0x11e42ade3b4a5910f677,0xf9ee44374a142698c774,0xc8b3a44fcbd24e6939bd,0x7f6d4c3d443902ac2311,0xa5d0e38cc50a3246e0f3,0xf9b67851ff9354d5fca7,0x576b7b46481d689e0865,0xb64174aaa28c4bd98728,0xad7e04f2c954bc2291ac,0xe21939a7514094fe151a,0x7070baf11bd569ae264b,0xe31ff4c18f3898fabc2c,0x8dcc12752bb87c97a48a,0xb50c8bfa20966cc3d8ad,0x6411b207783f8504131b,0xb9153ee470f41c11abf5],
[0xd51191f9df756c73b577,0x4d892f6f81e32b940271,0xd11510d3664562cb60d5,0x5de77f7803a07660e26b,0xb54e51f8f32cc9dcd55,0xde2c794ba6b018026ec3,0xfed36aa1d06757ea6678,0x3efd3cd86327f2175e17,0x32001fb09825b05c3d3d,0x20082d8dc049b08f1615,0x6cb2df4eec758987be46,0xe7b0fc5d5d61895d717f,0x833191b7b6175acc40b6,0xc75f9577af1fd1c71ebc,0xac34130b297cfb961a83,0x9bc40a187d932ee25b49,0x61f5d3f60ca29c4fc953,0xd5f6f5ff48d210b55380,0xf202182cdb4da11ce4ea,0xa105c2f20d60d60f53bb,0x832fe3e00ce534925c49,0x1703e505ecc862036415,0x6c0035e1052ca45a7639,0xd9151fdb7940ea00aaeb],
[0x10468a507a9608de0b72,0xa6f91f79cf2c7b8bcf81,0xbc0687667f6be5db7d3e,0xa7a66f0db05f3a196115,0x52d218087bd70d2682b7,0x74558364237a532c22d0,0xecd4795996587fd930bc,0x35ea3ab8594ba4ddfba7,0xfb6becd605221b748ce,0x732aebd52a25435f07a9,0xac3c9a6da28793624c50,0xaa3a0cfaf5a055901a6f,0x583c6cb731baa99504ec,0xdca5aec07edd0715beca,0x505ce00f8e5542af7c04,0xa22becd1591c8b28f81e,0xcf0d899177f0788879fa,0x831f1057bf2926324a87,0x6973cd7d0f776bd57b9b,0x64734cd27a51086e38f5,0xa594495aa86034e9435,0xd7a047765d609bd6121d,0x43412393ee14820c32c0,0x8913490d5fdd573d6eed],
[0x804df6da7e6c1ccf48a2,0xd2ca3addc55ffc400fff,0x4af9e96702f73ea14b51,0xa49534cedc0f5fd283da,0x35b3ed47f4791aacad13,0x5d4afb456849fb22675e,0x26bdd522192138d17563,0xd05929ac4dcc1b2f460d,0xc1fe6363e0c351f40a58,0x2da0e1cdb40bb8521279,0xe9f86d9ed135c6cd2471,0xcf5e62ab187de14c87ae,0x5e6f356d504fec08b65e,0x92f931475f9f7ea19d8b,0x5c787125b0497cf02055,0x18a5132182022fc0b44,0x2279eea109a0142161,0x26d5aa519b53c60a1400,0x2669f4bbfc0a87948f76,0x3d5c9c92e358419a7c48,0x66933b215231ff74074a,0x326f26262f86e51894c6,0x1ef09381f165612a389c,0x914d0efdffbf782a8f02],
[0xc0a07e6485e67b8f4035,0x489d882e104857417112,0x5dc52edd10e8d98ebf95,0x7e6f8cc0d543bd6222df,0xa62a91be7338c27625eb,0xaba39df51a48c943ab67,0xdaab6097a3b6f22288a2,0x765c0d045ec8e3fcddbf,0x794166afdd2e3494fc3c,0x509de4adc13201644604,0xcbe628f866c6ecbf421,0xb232ecffeaac7eaea5ef,0x1ab626f7c8a90bdb768f,0xd43743e9f3cf0e76dcfc,0x8f38d9f07f600cae0532,0x168c63a4d5daee0147f,0xa04ead66b805b2fa0121,0xe6010965244c07a14666,0xd51c39df7a41410ea70c,0x57eeea4060b32a1f785a,0xb9e14f7c75812e65a33e,0xb62bd2fa2d1603650b2d,0xfc29ee81bca33199f026,0x2176ae6a40b4ba995bc6],
[0x121b85152b83311a768,0xf1216cf78791099a63c2,0x9a99e171f06966223f40,0x2b87d5c90366cdee3f39,0x428d8303e63fbc617017,0x864997b8f703419f75e7,0xdabb66a751f4f75a5fe2,0xc5ecbd7971b18781036f,0xa55868d0613d51dcf90a,0x774ee46605225de2b55e,0x162bccf092743ca4ebf8,0xabec7c2bc32f22312073,0x9714ecf0c5b4fd9535bc,0x7c0e895f5112fec1334f,0xa907997c0e3f6ee88e92,0x9a8b1bdb0a3b11285205,0x3bfc6b30f66d9880559,0x5366cdd0778154ad9bb9,0x9a51993a03effb5b0683,0x9ee72944885e04ce44b2,0x35a471cc07f6213fcef7,0xd975220123012b68b0af,0xeca8dcc85292f9c1369c,0x1d167694e7aac1c3abab],
[0xb5924dd1646efda48fd,0x5a3f330c62b466bac20a,0xc46aa8e6fd58bfb1f7d7,0xb66ef9245edbda74e849,0x32e6b8ae24313077114b,0xd1fd26c41070afacb976,0x20b514a341c3ec11e55b,0xae32217df4d83b3db981,0x2abef30e02ec00f1d101,0xcb89c5749f350501f1c2,0xd53ad1523e26cbb7aff7,0x51e94341daf4675f3488,0xfdd8d159fd6d91437458,0x592b42e4dba9eedf1e2d,0x50b885fafca28d98adfe,0x1a3256084616de1ba06,0x58111c7e7361ffe84fe8,0x857cd48819adb38d23dd,0x3a057eca2d3efd8916af,0x286913f19cba07b0080,0x685c0a8f4558e7344daf,0xd598946d11f798eb41f0,0xc244c28734886b973595,0x4099332d92d6515d9a44],
[0xe8321243747b796fdba5,0xaa3384488f6b5ffdaa8,0xf4d7373d18550c0fbc4c,0xa57455a5eacc82d955fe,0x2140e947906d1d6080ae,0xdaee0185ad7573dcab42,0xdd755227da4a0d6eb102,0x520af8906642e177be1a,0xbc5ce10bf58bb132592,0x34b1c41efd50ff4b42b4,0x3c7044c75f1a9a1cccd7,0xad3edbc77a2649c9a140,0x1e6be231a4af1695303d,0x9b94cc30e51d9f180839,0x344d383e7e479afb92b1,0x4273139ed2d8c0ac984a,0x9cdda1ca95ec3ae2d311,0x2c0fc5c5766c85638b2b,0x75f744dd31bb3b81b6ea,0x7709a65f08480dbd634d,0x42c321c4a88681e9083d,0xedf8a21f15011245370,0x438fb314baff530e2207,0x7e88311ca97defc52e61]]

def tile25 : List (List Nat) :=
[[0xf9f44497b318c48ceb0c,0x2d18031d0a333af7c581,0x5184175b689738344b79,0xca864b4f0268d6c49b4d,0xb9a245774d9762866496,0xee641e7ef20a674c6040,0xfe290c6c064674238740,0xeb25172903a431cba92c,0x463b2ee153287f6360d0,0x67edc365d34dffde8373,0x4d7034506800a9f37b00,0x8c1de40459b6336ceb6d,0xee4d43dd7c9bbc0d025d,0x7a7cdac2bf36daad51c1,0xcc9748fc16b056911585,0xac941fae30ed7f33f2,0x82e6c8f9d14a33d02578,0x951a1261838f9324bac5,0x963baaa6c93b9f039884,0xe468dd943026a5f4aa19,0x1fa1782126f403a5e007,0xe5548a1ad58c7240e4b6,0xb3835f0730ce6a3b5ce4,0xa0e990d3747c7c913f20],
[0x51236207cfa875eac281,0xbb587a4aa8aed192aea6,0x631524c1a9bc401e4aeb,0xd399a0730339d69ea0c4,0x2d8ef862833335f9015d,0x59c8907d4ffba07b0872,0x4abe4e18a0e22daca1f9,0xfd79c8fbcd1a72a51d4a,0x74722b89d3346380df69,0x740e64dc0ddf9aa5d3fa,0x704dbd5ca73d61b6cdeb,0x12f2fc360b24f0c9e50,0x220084dd9af94737170c,0x42e8d2ec94be0363f823,0xbd87cce40a8d2160249b,0xab68ce96a02726d7c8bd,0xab413ee6116ee007e03e,0x7166bbdc5b2c40f46cb1,0xac906835183444f84784,0x9f3beeff8450ee3a4a66,0x9782326253296d8bd8b6,0x68aba62069ed2ae75b9c,0xe67b389ace9b1afa68a0,0xfadc4df82c3952e22ed1],
[0x615eeb99067e4931a699,0xa94a5174ce7cbf13dd0,0x36429ca2aeff5094a120,0x9fb8d67b4591d7c35153,0xc3ee270b37274388e67d,0x74a4b148ea1e89d21e87,0xb1b7b7f5f3437f103d1c,0x8671f8f0412a3955fb39,0x855d49d005f942ba34a7,0x434de62d89d74177ee0,0xdb40fdf88c9469d3d340,0xb98630aa857a551c8c94,0xe974d8cd8109634405bf,0x19d87dde507a8a43ed6a,0x5c5523200cbfc6635b47,0x208e70a7bbf81b20ea57,0x22de7367306482f73476,0xa53150a972c8ad1f954f,0xc18d6db0a54d344e6f81,0x25165d2673d82cae5b38,0xbd3cb9dedbc694326267,0xa51fca8b661d53ea055,0xecfb8517021085064349,0xcaabcc42f41a8b18fd7b],
[0x6c18aafac90748543abf,0xc54213e66241ec396406,0xd6f4f5a477ead70c0be9,0xc751baba545ec595afc3,0x45277e17ac71afed7eb5,0x6a103cb6d28a332b1a72,0x36bdc9066d46d0ed57b2,0xdb46a35de7a4bfb2b12a,0xdc0b734767097d0de1cb,0xf70fed333c2e213a9078,0x3248cfecddd7c0970ffd,0x113840dd9d6c7125e8b7,0xe668cc9bdb8f59e35b3c,0xa531a20cdb7c2018f059,0x330e9e3dbca8de3c22ec,0xc47b45a3c4d3d232fb2c,0x5f6866c8585143ab4c03,0x2f592daa4fe29fc373a5,0x9cd43a48ec82fc9104ed,0x293317c92e539887d7ff,0xa4cd486acee559b853fd,0x1753bc27afc6fc72c959,0xb5fd3974e4eb85f73081,0x9d622a56c02306d71a81],
[0x9019417f9b7fc68e937,0x89b21c734f8b08886ce8,0x979dfc84d1b774943e8,0x5f3a5ff70ec84b92d5a6,0x5ae4582dda475be64b89,0x1f98bf3a4e40957ff106,0xe6d693830ca8a11f74a1,0x5f617cb3d2dcc8b44617,0xfd4732e2cedf19b32f0a,0x157595414d8a9b103c07,0x91673a26243f89d8e24c,0x2d6f68de088c3847c88c,0xea56197a3b0698815713,0xe9c79e4b92552218ddab,0x107a2d1e3913e4de8cfd,0x235af7225fdf3a22581d,0xcd1aef210272433010c6,0xc1ae0fa04ffca0cfdd7e,0x6c3b0844385ddcbb01fd,0x3881a7b60bb5d74eb521,0x3d25bc4d844fb13cb62b,0x387328d7823d62c8379d,0x232b6732f53d98b15789,0xf2b739223ecf68ea395a],
[0xa870eaa84e12daacdf5d,0xd723b97bf7c4c5872e2e,0x2298ebf3675afc009726,0x6b2ad206841de16f3295,0x5d5f0971e07f42ad9342,0xc28eb7f8c9ab8ec3f7d1,0x639de732eff3797b0303,0x3a89d1509ad47a3fcd34,0x2cebb8a5ee4df25e99e2,0xb309f0a84f59326c18a0,0x94cfc89bf692cda4765a,0x75cbaa78182066c05afb,0x5569a72ab48cdf3720f2,0xd6496742622a6dcb3c36,0x89c38544291f210d647f,0xe8404fe4d347a27eb0b3,0xbea94660c7b40d70ddf,0xdbc968167d19ddbc2190,0x62de8667da0af0b5f6c7,0x2cf9b5ea9edf4672d11d,0xf06298a30ac3b2a24520,0xb30bf45be710c396f019,0xb7433a972634ced1400,0x74facb5b076ce0001b6c],
[0xc51da67091dc7e8d66fd,0xf052de601ef38b19cd0a,0xb80b98d5273c0d4bd249,0x2e35176c9558ea2aa9bf,0xd20a8ae082ec0269b52f,0xb3bb3905c2f2e458f688,0x5db99ff369a5a5a3f771,0x62d833c9cf72033665e5,0xfacbf4354017c476e0f2,0xc37fed1930e3bee154c4,0x730e615b946b31dafd41,0xee020dd800d17d1d8388,0x660ede99f84ff04c4d98,0x73a8e31d10cf0ca45e25,0x26e8726065b6625479e0,0x8dcfabc63cead44cad34,0xd72f103a589f6b86f66e,0x6ac620d006187671463c,0x7331a2e2f69e149bde0a,0x60e19102ce2126cbc60a,0xa45a2e1c46be9a1ec21d,0x58361099b6ba851b51dd,0x3cb8a2a6478bb36b7dd1,0x513f0e1b2c186e1abab1],
[0x27946d46f7aa8fbb5f21,0x15a15849d7889e8890a7,0x9e4068c39f8b4f62c7d,0xa294df86f8e0f096ef82,0x14137bf591cde71526e6,0x67e9ec06b607f67e71f7,0xd9ff89e1f4ea9a7827cf,0xd83035e886b996920958,0x1ccbaf7dfa3b2a2cdc40,0x1db079f22b9181cb0d64,0x985a457c80885472465e,0x5c37a63880bbfd95f710,0xd96f8e7aec89adaf7e0,0x9790eaab808af436d5da,0x8ea0c5c8a95468ca502d,0x7195202231628e49173a,0xdb1c17b26fe216514f0f,0x82fedbd9d7b18619ba70,0x5cb59617f13277c6223d,0x2b2da03b2320037795df,0xb882bda43a03e6ae38b9,0x6d2ede06442d3cec55be,0xfe997eaba91c7c9b3cfc,0xf4548d496581b760cf03],
[0x9e67f6c16a0908eec629,0x90a4f27c67eda7fa4b1c,0x22b70fe34939399c2c8c,0x5a1cf44c7943831c4d4b,0x97edc7be72c9cdf2de20,0x911c0aa7b61060455d11,0x3615ff91cbb9df5b932,0x67c35d870f546b297f96,0xede74c18e74da0fafad4,0xce235a642068e3486c4,0x5f00edf2dd66b7947a7a,0xc849a62cfc7671c02262,0x45a78e62002e46359a8b,0xa24e19737535f9276e93,0xa9ca8b5d7bd38f8b1c40,0x829f5395ebad756b4acd,0xda14d75bb49ce4f00171,0x721cc62432ab4ce0031e,0x57ca2c84bc876d338912,0x64a347e63663ff902e40,0xa899cdce0b44d76ea960,0xe5630b629cbda1d50e56,0xeb0b784be13ce0cb5cdc,0x5bd4ffabec9ebb37fde0],
[0xbb0d9164327dd491b09a,0xdf9dd902cfd4c844c451,0xf0d0a6f01ebf37df9876,0xc256e05b152721226c66,0xb57f9ba4f8f3a5224eb9,0x75d6ddfeac293e2d18ce,0x8483d5383e8a229dcd54,0x1ed316ca3f658a2128e3,0x6549dc47dba033db53,0xcd97aa5465479662c177,0x29b78e0374b934f20f6f,0x4574bf3f57c18b241210,0x8f802c3a555b6e064a3e,0x1cbc6b84a6e65024ba7f,0xeaf4cb936b5087a6bfdd,0xdf5b0e360343143289d2,0xdf89f1b336439953e85c,0x36a58a429c700b070f82,0xd58c50992c5a2a8d211f,0x5ca9aabe22c90fd3cb08,0xcaa17a99a5b27fbe1ceb,0xe6be45d456e0cfbf6fa4,0x93501ca07f4513b37f28,0x801f3b63c963e9397e17],
[0xf3fc20a5ba8a22aa5ce0,0x922a1e41eab090d6c67,0x2b0579dc5b4947ddb82e,0xa57ba3ddcf217388a0b1,0xd7c2943710bd7e25167a,0xf0966a155ccdd25a0f8,0xd3b6078d26c6ff7897b6,0x7c85d88a9ed12f7298b0,0x9d002949754e0ee90445,0x88214c45f211d46d7e79,0x264b95930cebb4986724,0x8759c5d6fff725137cac,0x9f9fb385f67586f05115,0xca7627342403b5fa0034,0x626b00d17cb38f09e456,0x3ce6e67826c2c6ab6fd9,0x4ad79ecde777f32d90dd,0xf21b6be224e9a0812627,0xe3b32c26c4d6c99b6b1d,0xf652f6fcb64a67dba760,0x87a7c8ec364615dea87,0xab1104b10a19220d6033,0x80b87cc641bdc60069e1,0xf64325cdb8d78244932b],
[0xfc72f31b190d168c6ebc,0xc9848e4827c0f94bc4e4,0x9627a588ed9b293092ea,0x34df4609d3590d3f623a,0x9f080a19e357b53b5775,0xbe0756e5d37102ce8c9c,0x4851515d31cc905ef89a,0x45f99df19729a2a8342f,0x5b18cf76f53ddf240907,0x83ed88c4e7e54433a4bf,0xa32e347173bbea43e129,0xf89e74c59d49a1c8c053,0xd96e5fa0c34241f2327f,0xd1337f5b29c6fb9009e6,0x6b750850e73b1147c67,0x3c66e650b3b09243d43c,0x114b68065e90518f2c8b,0x1008919512dff78cd33e,0x2d003b8b9a8071b33171,0xa0c509a59fb271dc7fe8,0xc26acf64dcf7840ac25e,0xb628244e8a3257c7c656,0x5f12b9ccb2ad9ed9b4e6,0x5f64b3db4a840b9711d5],
[0xc83becc9b94e963bf4d0,0xefd43203e9b69ecdbb7d,0xa8ab82b89aa1aea55cb9,0xe8547b4c490c583f282a,0x1f89d8274b419aa535da,0x742ae8e168e31710ef1f,0x877f099f246457f71a53,0x247eb8d23ef06aff94b1,0x713f14ce1803a54aef6b,0xbdfda1958c9d4607c72,0xd44c2013766383250867,0xda181772506a2321445f,0xdb70e2b97f2bd4768a0a,0x1a6b6535714f3f9e4dc8,0x26c9ae51ddb85b0fc941,0x95a06c586ca11703de58,0x79f70f05665cb09348b,0x472fe05ccb1be0965dae,0xafcc395d461f002e153a,0x9b2131a29032322ae2a0,0x9df8ebf033b8e7434219,0x49ef6e9796f4b39921a7,0x75d6c61df631b8122671,0xfd98c844b909e5341553],
[0xd02a871f462c5c4d352f,0xbb926754e8ee23003b96,0x2af2b8272d6e47ebaf89,0x150a20b88a44adad3795,0x643a9600b714d7f33212,0xbd1c92f529c60127a9ba,0x4fb0ef3d0baee595db7,0x6216ca61a37d796fe715,0x3cee67e1fc9f4dec5b16,0xa2fb817fc4fd928658ec,0x6d495449313041d0f4c,0x8454f44f26b0fbb429aa,0x232992ffc15bd46d69d8,0x3a8ccda6e551cdda3bbd,0x5df010f26da41c2e1e55,0x5a48b75daff61b136f9e,0x70f41737c4fc2e4cab1,0xc4785102b5f3b1c9ac1d,0x9fbf89f6f2b9ad1528bc,0x9e089386a858b4b1a4cf,0xf882b7d7624a1bf6ea11,0x2a6f9fd8e85a32b7335d,0xe3839081b3416f83a015,0x4056d878b57e3f31997b],
[0x66ce02f7eb0a5bad1879,0x2942ec86cac70a179646,0xe87fbb9e6161d26db090,0x3face4e5c4d955edfddb,0x64d1736b0fa25ef2fc60,0xdbb48da102b5b077e633,0x87814220109201d8b3e,0x557b3d7af9f24702fe65,0x3c7f43120da1517a9f19,0xfda5e6a4e7b56e130ffa,0x6dd7381486aba0d37dc1,0xc6958706b723fd391384,0x939fd495b8685ad63828,0x6f0ef8bea86f2aa93b4c,0x330edf801d640978993a,0x6203d26f69b4e21e4245,0x4e122c05aa91e0b1c09,0x4f74daa0f6a07d890847,0xfc250dd9832b04a07bbe,0x588e5e28fc2853b2993c,0xe06e3f878269aeb14faf,0x1710a07ba150a12aacd8,0x703cc7b7fe2da94fee5,0x55fec699fdc1068ab13f],
[0x6c5662e4a3337d8defbe,0x8d07ed3a7f88075ae5a9,0xc2110d0dae18db15a9b8,0xb5a26a97880df92b019c,0x65d5fbdb1e60ff4d06f7,0xa48c936045e3ba394801,0xb4ec799d86b73d38b969,0x65eb8ac8cc76719ee939,0x39126435c5ee28b01be2,0x4330ce56b9fa989079fd,0x2cd74ffe6523c21402ab,0xdac221ee754681fe9f9d,0x4b3353c152327edcd521,0xdf811d97ea223a4b1150,0x1f4bf0837b35aa22fb38,0x7e912d472ddc918b4adf,0xc19936b144cf7beee673,0x5f3a4fcd7d8e3ed47289,0x79110aca31ecbc18f492,0x2ed72fc330f274388413,0x330ce10263b57e4f558e,0x19621dc3ddd6773a657e,0x84a5a9c228acf16d6a9c,0xbe9e224227d01842e5b0]]

def tile26 : List (List Nat) :=
[[0x296a11e17f2409e11305,0x2e1f17c74f3dc15524b4,0x4b87a6bfa3370f0ecae8,0xf477307bdd2c8290f030,0xaa588b2b63c5bf829f0a,0xaccc73076d6a37dddaf2,0x11f529a8cb1a05020cea,0xb0f25869c9fe9cd4517b,0xb8cfddb2b30a2f9124c1,0x3ff8c7c6b56514e655bf,0x722ba8ba474e990194a8,0x9ae81a0dc665c96fd1e,0x11ae832681a7267f24b,0x50e004af57d35e74979b,0xb76533368a96f38b914,0x30320fd35d08e9f7001d,0x51acffb71d3a5ef36f42,0xc3e6a586cfdaf702cb24,0x613b7f5b7cb708f8b3bd,0x8f42218eff151388bf8b,0x37f129f3eba708b12d7f,0x7426a164bf656c26f662,0x8b98ab915eb37c35cbca,0xb26ff26fb979f8840326],
[0xda48452c0bfb96c2658e,0x4840bd84b4f33c4e4bad,0x9a44ab51b32f674856c,0x1ca27ae602f7bb314315,0xe6a4fd81c30154867994,0xeb03833206956afc0c11,0x61395a29f743e643804b,0xe7ed558e0ceceab948cf,0xd705f230fb94ee5e696c,0x199b0c8f3dcd806ba585,0xb53d8e0a732e80c83980,0xbbfc49cb335f05cc2f6b,0xe74664dbe7c39901d93,0x1ff89ce91a935e4d7b08,0xe69b61e00beaaf6e2b69,0xf180c4058c1e2059cb5f,0x7b3e2fc7ed49c7e2d57c,0x607a61b468a79d7bca46,0xfb8dad777dae9df2340e,0x310cf854fdc1b9c180c5,0xdb5a98257b2e5cf67ce9,0x40672a10b073df9b26e7,0x774c955e81ff4aecb2f5,0xa555338fadc975ac87c2],
[0xb68ce955926ea06eda81,0x3230144530f4ed70a174,0x11c07cb0d2f8009ec36b,0xda1788c8239010b3eae6,0xfd3d84f2884c341409fd,0x781a3cc3abf1ce05c4a1,0x7ffd94e82dd61d2ec4b0,0xbdab3867b84f63e82c69,0x5e66285df50d7125a133,0x400a378ef5796b75961e,0x1a252a4be5b0377e7dd1,0x8c93b46f7f1ead78e111,0xf8d01ea03e0fa9005a21,0xe08bf1008667c9bb7327,0x80513318f61479b2e025,0xe9d6ab1f4d987aee9988,0x913398c1cd176c0d94e5,0xe8cbc49b42fd9c0974c7,0xd7106f7a1da6601231ff,0x175169eed96c887ce391,0xe8a4939af42a698c7e48,0xec5f721aa8717df7f38f,0x355df1c3d357b2782d6a,0xf12233d46754d1f42401],
[0x568739fbc10f6f3f37be,0x5621093b3de2ad679324,0x2e216cd0102782cbf6ea,0xf71d3b84f9eb33b3451e,0x82d156afc3dfca3b462e,0x189129beb3864ebb0896,0x3c122020b0e44982ff98,0xbfe1f48e631f9a7390cb,0xa9c5d8808b05204026aa,0x8fe3ce58b152ec71b8cf,0x3611419736866bcd1da9,0x416b7fda19096c817920,0x783de4b29f85486813c5,0xf10267a5b0e125ef1fee,0x78d7ab8a36a741287b81,0x43621f118cbbced8f2f8,0x6b80bfaef958c2ddfd7d,0xc8e4d2d0681f5ae7e5c5,0xb7bf1b4159625d8fd50a,0xf90434d62459b90cfe0a,0x74c123b364a0169b43c4,0x205da4bde2cc59c9d08f,0x1515d6a32a7ae6cb3513,0x198b3e82c2bebd2935b3],
[0xeef67d05f062e18c72f9,0xd41d47563f07eb3ee5b3,0x96df320680705d95100c,0xed2bbcf9d866c9293345,0x30c03dfbf40c653e568b,0x182e3dba118587befac0,0x52d4459dd7cf594adce4,0x72c85e8b8121de10f20,0xf0f3d952c16abc7f98ed,0x281a24aaa7d5da7be48d,0xae9ab6d2bae60d97fd53,0xddfff97a3905e0523d6e,0x2f8d3aa6b6067ff5e1bc,0xf08e209ca73cce184476,0x1534804e3dc56c0061fe,0xd1718fc699f9025cdec0,0xdf2aec73abf0879f7cf2,0xf8cfecad27f830183bf0,0xf451ab7c79dcadf3ab4b,0x2a73a032ebe03d9ce486,0x6b594af341858e6f9ccf,0xd0db6b8c5ddec00b6fa7,0x6e360b4b4a31d47f5a27,0x39bdcdaeb1519bc9de05],
[0x783c83145ed190edba66,0xfe21872cadb2f4ae36d8,0x89b0f5c2f91705c4c4d7,0x16b7b5375e8d6e26e12d,0xeb7a8bc46ad742dd0401,0xa9811c384465ba3ae287,0x2298c1c58e5d0513b14c,0x6aa203a4573521e7e305,0xe0af1fbdb457c6d2fcea,0xc227dc2557b354b92cec,0x88c2cec52820f583a266,0x65435c8c74fd11039441,0xbafbae5d605e6f4f9167,0x84a9445b1c883951e9e9,0xd17751cbd352bef0bc2c,0x9b1dc7fdf68815444c33,0x85bcbdd82d429c0cefd3,0x69f3b8055bae2a7e2000,0xc7d6b64bde0f94064fc1,0xced83196571f958be1c4,0x1617ec4ced9427797188,0x8b681b8698ae609d1020,0x2522dce076c582281db0,0xfad87539c3a58705cbd6],
[0x31ce1dce5f581203347b,0x533d499aa2ff1cdaf48e,0x4ef955aa43a778734c93,0x875caa28ff08e2937b0a,0xc472f6bcf542ff9b1367,0x5b6d48d1e09062ee779e,0xab4c3e989c836946855c,0xee7b27246ba1ed42aaad,0xcdbafa9c4df7bc28e061,0x176169f56c4e0fbbd09,0x3970d1f9ca44fba2b81e,0xfd90677c10957644ba6d,0x69f266a7f891f9343752,0xd114c234e51b519ecc71,0xceff31c117639b6fe371,0x52bb9ea718525762e375,0x39b7fd2caec17c7aa2a7,0x5f34c9840f8109144f38,0xb6aaca4bd62916f63e1b,0x7123556350769fe1a43e,0x82df5e4ea91aa2c4e05d,0x575392be7497c85dfdeb,0x5d5a092c36fd8a5504c,0xe52ddd254eaea024fb93],
[0x510e9deeb8140399b0a5,0x2afd5540394d212651dc,0x966cb816909d86bee8cc,0x3671cfaec84855f3ac1,0xffc393aa5bb9dbc0bd5b,0x698798470c4c75bc0f8d,0x991bc711cfaeb6257744,0x3147d0811d5a449250d5,0xbb5f43d6aafc2143883e,0x5049798da8537c439ac9,0xd33da94088878fc502ac,0x858dec287acc82fb2d2f,0x40bc8e2dfc7b83e20d04,0xd1b47fe9c47a7028a4b1,0xe0336f79eceb9d3266c0,0x5848a35e630405930c99,0x94fa314810c7e0b18b3d,0x317d5e59f4b29c89ca3a,0x26c9fa8ce0f0ccbc9268,0xbf3e533324168e2be98,0x2d85501b05ebf4545db9,0xbb9ca65c91d2fa5eac54,0x5c28825f51cf8a78c8f3,0x43360a47cd11d0d03f62],
[0x6c38c7702c1001f87c82,0x5424dd822db163c0d62a,0x9e0d2e47d9de549e36d3,0xc9886a278ffdc8abb5a4,0x83aab00b1d08c9574aaf,0x6ca98086ae78760614a8,0x34cb7adbfcd7413a9ad7,0x9f7011ba4e7eedd78a0e,0xd57b6f6b2a88f7526542,0x259f5e6548c224b6ff4,0x150dee995a7b7ce1e2f2,0xcf892b19b509a2f4da1f,0xd49d764cbe4f672ef1e8,0xd373c9d86c73b4b17eea,0x36a4d983c370363caf0a,0x50bcb3ea58dae0258cb,0xc9c25d88290de0235851,0x695d2c55dcd5d1a0d68,0x806919c998c487c29fb1,0x6f6cf0c929e5672e0e1b,0xfe50e2b57422c15a2983,0x952231af354630e74efc,0x7cc68ad448e5cd0bd32b,0x71d514c1ec0bd4db576a],
[0x64df8a1b40835ac0dedb,0x51077cb6ce415a36e9dc,0xd34485b44eed33448c70,0x7c12783958617c86f2ae,0x55744947a8168577f04f,0x8411dce2e2792220aa5a,0xd4d0e1a196dafc80b946,0xf7ad2c1676641ca1ad9f,0xf7044b9d6bfc7f3200cd,0x7765b1b5a635f30d95dc,0x2260373c5fcacbac9a2b,0xacb45b0bb87b1b12d7bc,0xb44d1932336aa698801a,0x869572198fe34c55cef7,0xa13e9839ab3f43699753,0xe60bfcedac35aa47bce6,0x662bda37161ead236f4,0x3f3a956e2f7fc4e33754,0x13708fe6205c4de765a9,0x6c3f482c0dd6468b4460,0xf1d896085f6ccdbdb075,0xa4489e81f9ad550502fb,0x5caba98e2025c5652ae,0xfecc4e103ceb03da0c1c],
[0x9b35f8b43e3dbcdbca0c,0xe971452b038a4c398f98,0xb8bcb92208576905f888,0x2089cd9a7e89cc84e03f,0x3adde8482d864246bf20,0x58446b8f6fb9cc0d6541,0x42b890b5bf1e86e732e0,0xdc307ab7ccf6c3c801c8,0xb5190c3d22b3e200e546,0xbb308e4227776dce009d,0xc435ab8e88c757ef8e04,0x990834fd8667a944114e,0x42ad7366d4caf4caff6a,0x9906c658fa27e4738267,0x1180f77ec3a0b6708253,0x27b0d1e7dce75cb0c8f3,0xaa4907890361a4d3318,0xb7a8542c2fb2bffa955e,0xc2d1c8621c6842ed2003,0x56819a38535652beb5c2,0xb7ba86e212aabc9d9b7a,0x11cc53f3e546181bf6fd,0x8bcc45798fb9dc7d6ac5,0x25e5fbfd97180a3d26dd],
[0x8bcfa7f4b17b7efdf2a9,0x69bee946a0b169a13433,0xaa8076cacc987b4c65f4,0x9f5dd321694c7400b74b,0x37edce0065a028c37794,0xab1d2d5ecdb5c8044f96,0x5df07419ad395b92b3cf,0xae18b83f46bd5ee58a5a,0xc76f4433ef7669247f33,0xeb6e0c6cd96353dbbd48,0x41ec41ccfa5ade9d4ed4,0x25ed9ff0859b96a0f239,0xf555ab21c6342d991003,0xe063e01f7fe93502178c,0x110656e64cc35ddec8a3,0x4474b3b086274fbf31c8,0xbd9aa4c5538101028676,0x91188449472f21c84793,0x6bcd18162ccc7a303262,0x90bfe5f91ebb6e129e94,0xcbc0c5a8569e7e93f8eb,0xbd41188debbe50eb3b8,0x796588eaffd91a07ab6e,0xd1389c5756921dd41d6],
[0x5c34335edab43d879720,0x15165f9fe6cc6863d8a3,0x73cc9d9d690e64a1ed2,0x1dd8ecb4385bcd31caef,0xc2ab4a1cbd21673e8589,0x4d3aca5e074c8a5f8c9c,0xbf50a8e37f87862f1091,0x2e7751babcaf2606190b,0xd6985c02db6e8e5538fa,0x866f5c32498554d6da33,0xc5517333e3d300b40c0d,0x659bd24cabf4dea3be24,0xdf17e217e0b6ec143a58,0x80b699e5afc603cb30ce,0xde6652bc9db0ec20aaf4,0x9a6a67f59c701300377,0xf7c011167b5c923bf016,0xf1afe06578363bb6a950,0x87581e1563701e890046,0xa36ab8121d893081af4e,0xcaf59dd4f1141201b3c2,0x603db9cc02e06732bc1c,0xa10bea9d1e36899902b4,0x6f9ac9d989ab866cdac2],
[0x908fea97151ac3da4c4e,0x266654e499b61639d8e3,0x8d45c7d90eb12cfab3a1,0x53badb4c33ecaba6a46e,0xea23b4139c9cf08f0871,0x966fe0e40d47d8b2a813,0x74a275b199c6de449501,0x573c23cc8dd6d8ef25dc,0x6624540077e43d56e4f6,0x871db638b6eccfdfe4,0x60d4ba147b9d2e422430,0x27c1a169a8c2fba144a1,0xf35a532b841a6d35b083,0x24d7cfd5eacc7e78a851,0x883d9d3c2de338f18fa6,0xf64ad10920c379ccc591,0x818a8ebefd5b5c1be1be,0x3f9ae6c1e98dbc75de22,0x646042694d9a728c625e,0xabffa8900b9133a8e3a0,0xb90a592a80c7d7447db4,0x93f85425b89e689f6a8f,0xfbf989b3345c0d5e7617,0x245e0b6036fed5e0d2cc],
[0x6cfc2706cab29bd07978,0xd92843f9117d8dae8919,0x453fb3375f3a98d84160,0xc5973ebe24b3f54bfd97,0xafd28d5066009828bfe7,0xc6a0b4374c99f97378d7,0xc87bce50b67671a19716,0x52e277068437cbf3b516,0x2da76c0a59e02eee41e2,0x88a41c666dca5404008,0x28835c791aa1fbf59220,0xd171c0757d115d9eeb70,0xbf2bb359498ed8c77e54,0xa13a0dcf7e7d5393be6a,0xe31d7ecbfe08026cd5f8,0x16d211df0e206ede1477,0x544e38d43cc3fe4360e7,0x7fbd58e211f460e10512,0xa6983002e45575569a8f,0x1722134e7fddc0d145ae,0x77098f1a876e0e2e26a3,0x293daacda88928713ab1,0xfe31e73f965ff87f718f,0xffcc8d4d58e206e32347],
[0x613364c9577e483c9169,0xc3aa3455f785feed8723,0xba72ab70a490eb3db92f,0x3cafff86a84d190ea080,0x1c265c402d3c724e79,0xc837e1fc48031ebc93d6,0x882dea78fb5f2f5790d,0x4fba397c694a468b0b25,0x25eb7afd27ba3da98871,0xf840fc1dbaa301240c0,0x6ec93bb8cd1a23254461,0x581e564e5c83d94e4a0e,0xc3f3656acb6e6bf6fdcf,0x90f646a106da2f6932bd,0x941a7981251235eb115f,0x1452cdd36f3d2b5c8bf2,0x9e99c9da584a9c300cf7,0x9f3a18c40b7141f4c1d5,0x8834fc7767c768229cf3,0xfbb181c4208b70a1c242,0xd9198e8b0a5a9d5753d8,0xbfa90600765de95c1f27,0x3e61bdae1b68dcc626ec,0xf86912c218df1183053]]

def tile27 : List (List Nat) :=
[[0x8aa65103532f6c587eb3,0x13a736fcbb6874313d63,0xca61ac18d9e96ee77dce,0xed783be9ac1b092aaf9d,0x1573aca7e5cb94df5372,0x8fad76684e4ecea6a1c,0xf307ffd8267d97994135,0x4d9836e66d600eeff060,0x893af55dbc596a15d798,0xa7444849a10fb4606d3e,0x9a2403aa91ae30d6fb1a,0x8a340f342bee6a5c6400,0x2302dac41b2bd9505b73,0xefb76299a9aa3f7e8793,0x8e26370ce017b7e67bcf,0xf9a3aade00770a8ebabb,0x366c7408474c7a34ef4c,0x6cb506248344ec719107,0xdf1aa78a8ec9a12beba5,0x9e5c457b027f822d31d8,0x58bfdca2c25905083b51,0xb6d0deba74d523ab48a,0xb8e06c86abb4567a392d,0x9ad688e4d1306bdd040],
[0x7faac45cd2144179fdb8,0x461acfda78dd4687c28a,0xcb4498ae0f064534409c,0x2f2a1c79af03ae67b019,0x70def818825458a096b9,0x244d594ca2c5285ab531,0xf3ac5b3fcd07b00f6671,0xf161a70b8df66ed53581,0xda004cfc5f04965a8694,0x1b504b13f43d8f4ef6a0,0xb10cd2aef887de322898,0x462ae150081f5418d4bb,0xd2998410ddfbc8c05976,0x91f321bb985baaa0ebe1,0x6d2a870a8574ddd41af1,0x21f8695dc5f3a1530379,0xa96a69ff0a8fe78e906d,0xf6e7601c72a4fc0fd80e,0xa1c848d7909338782025,0x1b37a90285108ee145ef,0xb2025b50c78fe7152f79,0x8ae0cb7c06228ce313a1,0xa4d9c31165eb128ee4e5,0xb0b7abfe1fa7c67a7936],
[0x3a4e4f4a2efa062440e6,0x7d0820fb06750af9280f,0x1ff3b0c689bfcfa70dbb,0xc3e259b2921894d6f4e2,0x2d7413ac96df009dd3a8,0x9216ca28b5b01ab23115,0x4ac2f141a1ddddad2e00,0xd98421d8047317f80497,0x45f93b65720a22397b9b,0x130d5d71feda07a86607,0x8e88c9262882411538c2,0xc540ebd5dfc97c94d47f,0x62d14be6681d92ff23a9,0xb70258d77bba5ed515b0,0x641a3432bf1c3f9b3f82,0x1015591e916ee1b33668,0x4ef71ed14ca66aaae617,0x3adc9c0eb1d74d105611,0xed5cdade62d81172111d,0x73f235490c045465c27b,0x361d979de41a1c589375,0x5079cf712eaf4e15bec1,0x47e25fcf48b5cb34d973,0x58d92d56ad9e089e6fe0],
[0x762ffbae62d2dfb1aa2b,0x3cc1c1babebb30bd4071,0x67f5cdcbedbb99d3ddf5,0x4e34f59b18b75640b089,0xa18a8e59212230972812,0x3082db93a481b9afc230,0x800b3270d2e50ad6f716,0x4fff51d2c85a5e98f77,0xdccbdda191ecc1bc90a2,0xd2818bafb7a91264edff,0x99b358c0b23917d61de2,0x10100000b35067ca91f,0x40100030100020100,0x1000701000601000501,0xb01000a010009010008,0xd01000c0100000100,0x1000301000f01000e01,0x12010004010011010010,0x140100000100130100,0x1000401001601001501,0x1a010019010018010017,0x1d01001c01001b0100,0x1001f01001e01000701,0x23010022010021010020],
[0x260100250100240100,0x1002801000401002701,0x2c01002b01002a010029,0x2f01000f02002d0100,0x1001301003001001101,0xf010032010015010031,0x340100110100330100,0x1001a01003501001301,0x39010038010037010036,0x3c01003b01003a0100,0x1003e01003d01001d01,0x4201004101004001003f,0x220100440100430100,0x1002401004601004501,0x49010048010021010047,0x4b01002401004a0100,0x1006201004d01004c01,0x5101005001004f01004e,0x2a0100530100520100,0x1005601005501005401,0x59010058010057010021,0x4602005b01005a0100,0x1005f01005e01005d01,0x63010062010061010060],
[0x660100650100640100,0x1006901006801006701,0x6d01006c01006b01006a,0x7001006f01006e0100,0x1007301007201007101,0x77010076010075010074,0x7a0100790100780100,0x1007d01007c01007b01,0x8101008001007f01007e,0x840100830100820100,0x1008701008601008501,0x8b01008a010089010088,0x8e01008d01008c0100,0x1009001008f01007701,0x94010093010092010091,0x970100960100950100,0x1009a01009901009801,0x9f01009e02009c01009b,0xa50400a10100a00100,0x200a80100a70100a601,0xad0100ac0100ab0100aa,0xb10100b00200ae0100,0x100b40100b30100b201,0xb80100b70100b60100b5],
[0xbb0100ba0100b90100,0x101370100bd0100bc01,0xc00100bf0100710100be,0xc30100c20100c10100,0x100c60100c50100c401,0xca0100c90100c80100c7,0xcd0100cc0100cb0100,0x100d00100cf0100ce01,0xd40100d30100d20100d1,0xd70100d60100d50100,0x100da0100d90100d801,0xde0100dd0100dc0100db,0xe10100e00100df0100,0x100c20300e30100e201,0xc40100e80100e70100e6,0xeb0100ea0100e90100,0x100ee0100ed0100ec01,0xf10100c20100f00100ef,0xf40100f30100f20100,0x100f70100f60100f501,0xf90101750100f801016d,0xfc0100fb0100fa0100,0x100d30100fe0100fd01,0x20101010101000100ff],
[0x1050101040101030101,0x1010801010701010601,0xc01010b01010a010109,0x10f01010e01010d0101,0x1011201011101011001,0x16010115010114010113,0x1190101180101170101,0x1011b01011a01005801,0x1f01011e0100ec02011c,0x1220101210101200101,0x1012501012401012301,0x29010128010127010126,0x12c01012b01012a0101,0x1012f01012e01012d01,0x33010132010131010130,0x1360101350101340101,0x1013901013801013701,0x3d01013c01013b01013a,0x13f01016a01013e0101,0x1014101012e01014001,0x44010131010143010142,0x1470101460101450101,0x1014a01014901014801,0x4e01014d01014c01014b],
[0x15101015001014f0101,0x1015401015301015201,0x33010156010131010155,0x1590101580101570101,0x1015c01015b01015a01,0x6001015f01015e01015d,0x1630101620101610101,0x1016601016501016401,0x6a010169010168010167,0x16c01013f01016b0101,0x1016f01016e01016d01,0x75020173010172020170,0x1780101770101760101,0x1017b01017a01017901,0x7f01017e01017d01017c,0x1820101810101800101,0x1018501018401018301,0x51010188010187010186,0x18b01018a0101890101,0x1010c01018c01015301,0x9001018f01018e01018d,0x1180101910101500101,0x3019401019301019201,0x9a010199010198010197],
[0x19d01019c01019b0101,0x101a20101a103019e01,0xa40101250101a3010123,0x1a70101a60101a50101,0x101aa0101a90101a801,0xad01017a0101ac0101ab,0x12000000010000000101,0x100002b000000010000,0x100004d000000,0x690000000100005e,0x100008500000001,0xaa000000010000a000,0x10000b60000000100,0xde000000010000d30000,0x240001920000000b0000,0x10002d3000000,0x3880000000f0002dd,0xe0003c100000004,0x45d0000000100044c00,0x10004be0000000700,0x84000000100004ce0000,0xb0005c5000000050005,0x4000620000000,0x67e00000001000674],
[0xb00073700000014,0x81e000000050007ad00,0x30008670000000500,0x6000000070008970000,0x4000971000000050009,0x10009ab000000,0xa02000000060009bd,0x1000a2f00000005,0xa7300000005000a4000,0x6000a9b0000000100,0x3800000005000aeb0000,0x2000b8800000007000b,0x4000ba6000000,0xc5900000005000c06,0x24000fa30001003f,0x15f50000004f00131b00,0x170016fc0000001800,0xc10000004e0017b70000,0x11001c7e0000002d001a,0x6001d62000000,0x20770000002e001da7,0x160020a000000002,0x21730000000100216700,0x10021d70000000600],
[0x2d000000050021e30000,0x10023420000001b0022,0x800234f000000,0x23a50000000100239b,0x10023f300000007,0x2442000000050023fc00,0xd0024ca0000000900,0xdc000000060025820000,0x4002624000000070025,0x1002660000000,0x26970000000500266e,0x10026c800000004,0x274b000000070026d400,0x110027660000000200,0x3a0000000100282d0000,0x1002891000000070028,0x900289e000000,0x294a000000070028eb,0x500295900000001,0x29c20000000500299100,0x30029cd0000000100,0x5200000005002a120000,0x1002db000930056002a,0x36002dbb000000],
[0x302400000006002fcf,0x500316b00000024,0x32fc000000220031bd00,0x3100334e0000000600,0x26000000040034eb0000,0x60036380000001c0035,0x1c00368f000000,0x3870000000030037cc,0x100388e00000001,0x38b4000000010038a900,0x10038d00000000100,0xee000000010038e30000,0x9003910000000010038,0x10039f8000000,0x3c9300000018003a02,0x2003cca00000002,0x3ebc0000000c003d7900,0xd003fe40000001b00,0xf20000000d0040910000,0xd0041740000000d0040,0x80041e4000000,0x427c00000008004234,0xe0042a700000002,0x43a90000000600436800],
[0xb0043bc0000000100,0xaa000000060044700000,0x8004505000000090044,0x2004569000000,0x47aa00000028004580,0x70047e900000008,0x48460000000100483b00,0xb0049eb0000001c00,0xd800000047004a6f0000,0xf004d840000000d004c,0x29004df2000000,0x4fa900000003004f8c,0x10050ba00000019,0x511e000000050050c600,0x400053540000004600,0x9a000000230056500000,0x70057a4000000010057,0x10057e3000000,0x5823000000070057ef,0xa600630059890000001f,0x5d2800000005005cd400,0xa005e8b0000002900,0xd30000001b005efc0000,0x2c00632300da0083005f],
[0x336004b006681029d00,0x6bb80000001c0069f9,0x31006c0b00000006,0x6e4500000007006e1400,0x1a0071990393005300,0x95000000010073850000,0x100743c000000120073,0xb00744c000000,0x782e043c00670074a4,0x50079030000000d,0x7aa20000002f00794e00,0xa007ab30000000100,0x2d00000001007b0e0000,0x1007b4c00000001007b,0x1007b6b000000,0x7ba700000001007b85,0x1007bc100000001,0x7bfb00000001007bda00,0x1007c170000000100,0x3e00000007007c370000,0x1007e8d0000000b007d,0x17007e9c000000,0x802100000003007fe4,0x70080d30000000d],
[0x815e0000000200811700,0x100081680000000100,0x6c0000000500821c0000,0x10082c7000000080082,0x70082d2000000,0x83b800000006008355,0xa0083c100000001,0x84910000000300845300,0x50085470000001000,0x9000000060085bd0000,0x8008641000000030086,0x60086d9000000,0x87bb00000005008756,0x300882600000006,0x88be0000000400887600,0x70089110000000800,0xe6000000090089720000,0x90089f1000000010089,0x5008a98000000,0x8b2800000007008adc,0xa008b8c00000007,0x8f6d04d1003b008bf100,0x700931f05c1002d00,0x210000002000939e0000]]

def tile28 : List (List Nat) :=
[[0x700952d000000010095,0x16009575000000,0x96b30000000200968f,0x800984d00000018,0x98ce000000020098b600,0x40099b70000001500,0xf6000000230099ea0000,0x1009d040000001f009b,0x7009d11000000,0x9d7700000002009d5b,0x1009edb00000012,0x9f3500000005009ee800,0x400a10e0000001a00,0xde0000000c00a1760000,0x800a1e90000000100a1,0x100a24d000000,0xa29c0000000600a257,0x100a3f30000001a,0xa4830000000600a40000,0x100a4c60000000700,0x3b0000000700a4d20000,0x600a5460000000100a5,0x100a595000000,0xa6030000000500a5a4],
[0x100a6790000000b,0xa6f10000000600a68500,0x700a6fa0000000100,0x730000000200a7550000,0x100a84b0000001000a7,0x600a858000000,0xa8ba0000000100a8ac,0x100a90700000008,0xa9800000000700a91400,0x400a9900000000100,0xce0000000100a9c50000,0x300aa270000000400a9,0x1000aa70000000,0xae4c05d2004600aaeb,0x2400b0490000001d,0xb2110000000500b1bc00,0x700b41d0000002d00,0x730000001800b4660000,0xf00b5830000000100b5,0x100b619000000,0xb67d0000000700b62a,0x2600b6cf00000007,0xb8af0000000400b86b00,0x400ba350000002c00],
[0x550000001500ba7d0000,0x100bb680000000100bb,0x200bb7c000000,0xbbbf0000000100bbaa,0x100bbc900000001,0xbc000000000100bbec00,0x100bc0c0000000100,0x340000000100bc180000,0x600bc3d0000000100bc,0x200bca0000000,0xbcd70000000100bccd,0x100bdf90000000d,0xbe6c0000000500be1b00,0x100be7e0000000100,0xdd0000001000be8f0000,0x500c10f0000001300bf,0x300c151000000,0xc2000000000e00c17d,0x100c3380000000c,0xc38e0000000500c34300,0x3400c3980000000100,0x5a0000000100c64f0000,0x100c6a70000000500c6,0x100c6ba000000],
[0xc6ef0000000100c6cc,0x100c76e00000007,0xc7930000000100c78200,0x100c7b60000000100,0x580000000a00c7c70000,0x500c87f0000000100c8,0x1300c8ba000000,0xc9b40000000100c99b,0x200c9f700000004,0xcb080000001a00ca0c00,0x100cb5e0000000700,0x910000000400cb690000,0x400cb9c0000000100cb,0x200cbc5000000,0xce370000002300cbdc,0x200ce8000000009,0xcfb70000002400ce9400,0x600d0160000000800,0x650000000100d0580000,0x100d0f30000000700d0,0xd00d104000000,0xd1dc0000000400d1a0,0x2200d1ef00000002,0xd4d90000000100d4cb00],
[0x1500d85b072b005b00,0x650000000400da330000,0x1200ddb70808002f00da,0x100e000000000,0xe0b50000000d00e00c,0x1900e0df00000002,0xe3750000000800e32100,0x400e3950000000300,0xc10000000100e3b70000,0x100e3e70000000400e3,0xc00e3f4000000,0xe4940000000100e489,0xa00e4db00000006,0xe5580000000100e54e00,0x100e6030000000700,0x4a0000000300e60d0000,0x400e6540000000100e6,0xd00e67f000000,0xe74e0000000100e742,0x700e79900000006,0xe80b0000000500e7dc00,0xd00e8280000000200,0xd10000001300e8d20000,0x200ea080000000400e9],
[0x800ea31000000,0xed9c086c003200ea82,0x2b00f1040922002e,0xf40a0000000600f3dd00,0x500f6ca0000003c00,0x390000002100f7010000,0x900f8470000000100f8,0x1b00f8a8000000,0xfc990a3d003200f97c,0x160100360abb003e,0x2b20000000401027d00,0x1001052d0000002a01,0x340000000d0105cf0000,0xb010644000000010106,0x10106a3000000,0x107d70000000e0106ae,0x1801082c00000006,0x9850000000101097400,0x120109dd0000000a01,0xa0ee50fc00750b230000,0x864419cfa62e88589e05,0x3c5f5f429e5761e0f890,0xf5699d13c29cda3659d1,0xc85fcac5bc8fc7255702],
[0x69bae7efd46e05748c,0x513e0332f5c62a13be3f,0x2fb6723b6e33e20592f,0x88cb337c62b927bc34d0,0xf0099bae5a8da8c75b1b,0xe4b337c1517f04d001ed,0x64dd72faec08b636d590,0xf162edd0ad8a4cc08780,0x48f77bcd9bef5797d304,0x1ffa00d38e18d567b1ff,0xb36e3ee3bc3549aec08f,0x3593f61dc49083206b95,0xd6fcf5b6112e043ca79a,0x5647c7caadfb165622fb,0xa5a5d7710efa311eff53,0x4ce3105d6ac3297edb1a,0x6f7fc96219f04685f974,0x97b4cbd99a18487eab2f,0x801040a2f4e5ee933430,0xc9482bd80502f600c0bd,0xdf1a02cc9880b325a02c,0xfdc12cfe20df260df220,0x2c401348b20020c2ca59,0xd626e09de8960f4f3b09],
[0xf813f610980cf6272fe9,0x32d268cdb5de00d3624,0x95588d19bdf81e48428,0x9c8024cea0983005,0x99adadb54bcb86801a00,0x659f959b771d2f321,0xc8551677700001bb3f26,0x75b8fe98e309c0f382,0x680a7f3cd415df2cfa8,0xe2de8b48843a1aac0bd0,0xd9cc1d1e0f9cbfd1ed5c,0x423d9fa83d933b0ba3e1,0x300e851b20ee8a519037,0x75006b6a427d596e8183,0xac116ae3f400122191b7,0x511ed921675c7a0d96ce,0xefd1f66cb6b1ca2dd9e4,0x47d29310f84289e748ef,0x1bd6728e87f807d30fa3,0x1867210daf7cb97e79a8,0x40089bc458edbd739810,0xe2cd4acdbd968043b6ae,0xf01f0a2fa440b1604891,0xf02b6d5c730d550e7920],
[0xd25544b385400a039e7b,0xe00d7111bec22c001092,0x8cc41fb6ee8518be6490,0x8b270757ba4405dd6742,0xe2c640eec9cee14e3340,0xb10ec4bffe218b286336,0x7185620c6ff8812e1f42,0x5acea751faa5c35a5881,0x19c1fd49e7d32165336d,0xa9c7493b5e16719cf576,0x2fe30bb40665521700b2,0x97d791424197330bf0f,0x3386c0b0a70156eb59ac,0x3d8ccc58e09aa4f2782,0xc812fb2582a6e8ea0de5,0x3a9cb875db4b6eb5e66b,0xdc952e19985f879aafcf,0x7e79f4e546f5fe559ada,0x29db4b6eb59ac0d2bec9,0xd3d03ac9adac5ad3e52e,0x6cfb410bca440b500218,0x5d5375f69116ebff90f5,0x87c10acf73b0bd6e8157,0xfa7ee0da713e98f71cfb],
[0x7653a705035f8d0d331f,0xa18d259b6ad6753a8c1,0x64bd307676394042a7c1,0xf4042b83a54aba939ef4,0x3e8e08563fcccb3062e3,0x4f03db210a4ffe8e0850,0x70b16107ecb80588dbd2,0xcb0422f1c2030cf9939d,0xbe920d7e048849da7cad,0xf68547943d57a0bebec6,0x2e1e8fad0ffd83cb1a5e,0x1964bc714b4468bdb49,0x4b31aad708956634830b,0xc47bc6f22365a0119c5a,0xd5c1d3fc00e113c6a5a8,0x6cdbf4a7b5a322d09697,0x6022c3116acd6d6436a7,0x11225c2bc277d9af94dd,0xd3f7f9d07b5b966355ae,0xae33a89e1962d7a05780,0x16b7fd587d9d5f182897,0xa1cb38bc135e8d6b1d71,0xb5ac75c45adfea303077,0x846b5bf1e27d69c219fd],
[0xfa5e01778b569ee5150f,0xad3467428d857c2443b7,0xa99ff721e1f11b181996,0xadfe83db3266bfcde83d,0x76f123f4d2ed30f0a339,0x7d181796a946ff7ef4b9,0x489d029998af01499e3e,0x3487c0c33c19841d7813,0x1b81adf6b87096f66dea,0x46165f21541ba763f4,0xc99192ac1723e14bbd39,0x2dd59f136e321c610ea3,0xf9e0f6a72c4e50eaa884,0xa62d5b36c836dd7dffb9,0x27ff2095a19b3047e09c,0x96eb1e5034943faa275,0x652394d93a84cfb8f2a0,0x26fd1fbf39f40e2a97e1,0xf85783233cc34be382c4,0xe5b799d200abe2c443ad,0x2adfe8cf0a3171a25e4d,0xbac8fc5363159434981a,0x4927299b609006ff46bf,0x960b74e33b79d022c522],
[0x674a4fa9c91813118865,0xc88fb3a794f3e4db561f,0xd85309f23ce90595ef35,0x91a88c11a826d2dbcf68,0xb4be48a9114eb081601c,0x8df053777c0eec9a6349,0x9c70f26f1fe29525ba9d,0x3e69e1e7c1ddb9c3f226,0x72aad28645ac57d77d5d,0xff8dbbfa1aa5c3bbf356,0xf753b5f178043b3ab755,0x72d0e0366d5152e2ec0,0x4c00d1276bb2d759fc0,0xada0f1deb5a008047201,0x91ffe019acdd68346ac6,0x2c4a8a5b5a954031db82,0x6823c6b5cb0222c08260,0x17e803f397a03bdcd000,0x1843e20c61f4000000e9,0x5598e776d1e7fd07934,0xdc59c8e5b4c2f582ee30,0x2b5b58ab9dd9b71ef636,0x5591f5efadf21da85c3e,0xf46de7b46c0dff71f308],
[0xe828766dab14537b3b00,0x89e3d1a449c6bb02dc1,0x3a566dc7bcf6778f1e88,0xcb73c566dc7bcdf7e517,0x78234c08e59848f8b3ef,0xb2cc6264d2519ddde7c0,0x7bb17f1e30b5533d086e,0x2d12b043efdd1a49e7ca,0xf1bf07528ec409e6631d,0x229017e15c2245accbdf,0x2e5efb95ed202f62fc11,0xeff8dfaf7fe8327b632f,0xe1f53850c0eff4930055,0x22c7c77aed8c458478be,0x91aaa42a59cbc34b43fc,0xc3e04cc9ba261e1a172,0x21acbad05c8d82acaf66,0x2fb87d58103dfdbfaeea,0xe947899e46d5e3f1611e,0xca46aa90a9657b2d2c4a,0x9830f813326e89878685,0xf1fb234ba172360ab2bd,0xd586a89a3c11ac1e6f1b,0x6f2cdbc5691100ebcdb8],
[0x194f3ece0f7f1b17c02d,0x8518582bf6cd4adbab3b,0x1252f7bfe37e0a1524e7,0xad4beb060dad87084939,0x92172c9f3d16a6091fc4,0xc6ff69a34c77bfe37e30,0x38b4c55222e11ac74bb8,0xec69f2eba2670bcde369,0x6ef921d804527191bfc0,0xaef62340e5d7afc242fb,0x3346feb716b45901dfb9,0xcc49b8b0a2657245c745,0xdc28e9d27b9c7a86f50d,0x3b49c1a9a40aba8228c3,0xec0e939496a8406ed101,0x54470afc8d65d700af2c,0x7695e7046732b4a8a86,0x551e4c887ebc4efbf6ad,0xb8cfa46a589a8dc5f9e1,0x587a75f1054bd30a304,0xd1da233f68c57da76277,0xdeba0e6af36eae42ae68,0x80744e06cf2e499c46d1,0xcafed0e71e82d61db9a7],
[0xea4b26fd18adffb331ca,0xcfda44fd4010ae41a292,0xb0c3a484581ff416f533,0xe4c1d2cd27b5bfd63040,0x9a276851403d258df9e1,0xa5ad05ac1e14a068bda3,0x1ae008c4d2ebb768e744,0x4455d28ddfbaf3389571,0xee7a81002d6c5ccbe9b9,0x2d2d5cd224e1e509bbcb,0x39b08ee2289ef176e30,0xc222a1ac714faf4ce261,0x206b9a7f7afb5f271dca,0xd6d1bb3ba77abe0b6f4c,0xd6b6dc5fcae55e8a9068,0x7843453a095a28299e07,0x6b6b16b2c129f11f098b,0xf6a7d1015ec35c010ec,0xc1f6b8058c7c7729961e,0x3b2725226a6835dd547a,0x5b3c2dfdc2489a9a0cd1,0xeeda74c3d798ad96e34e,0xb58ad98e3f0a64d72336,0xbea60da2a9ab31f99847],
[0x11e5f48816ace86a8374,0x4118766a3e6ee5f715b9,0x364a088cbf735b911eb5,0xec210daf5a24111d4f8a,0x9689001123a7712d1783,0xc504bac05f4c54c9d46d,0xb90c4a2b318f53b52a1c,0x4cc002a3fc625ccd5a90,0x3c8bb999b177ee43a4e1,0xa56252cda2e39dac9797,0x62432a657749324bce36,0xfd50f078eaaa9529733d,0x7802cbca02243e10a23e,0x161d02c4639daa9a4096,0x831dcc0ed51c320899b6,0xad511118e61ba29988d1,0x10702cab290a25f010e,0x9af0083864e96615901e,0x8bd1f20d05321b6ef9bf,0x8a9068270134d8182534,0xa668bd8b77fa9a2dbea3,0xc11a71a8c63afef57d5c,0x8b176997eff8610eabef,0x4252a1a535d62f5caf40]]

def tile29 : List (List Nat) :=
[[0x34bc6b7cf128adfd71cd,0x926b0202845d6c1460b7,0xa1a865c1a38e4c649c93,0x4282000ae4eb002d9001,0x2c072553b99f47008607,0xc3abb32103ac520d52d8,0x7d33f40b870e44abb11e,0x1a7334bfc172025c8f79,0x7b820508ba72bbeec4d4,0xa59603b22e49c93c2492,0x7ef5029b575da86075,0x5c86e013f87c55302a98,0x40a0a265ce432e4d4001,0xd797717f1100d76026d7,0xc4975f5bfd4752041885,0x21eadec3f4c4a6f2148d,0xca97fa89a9515ea95ef4,0xe39175af65875d7d0357,0x494b35b5a7cb9e3bf7d9,0x64a506ad5fc591cd2f8f,0x71d9b7b2d01861413151,0x20e126a69c2c3c1ec585,0x1fad224e3534d761e196,0xa85523eeb4c2b7a28fa9],
[0x9ec2ec4483ed89194a1f,0xf534cf51211b1a184f97,0xa69aec432bd6d0b67fe9,0x3ddfd93a9a6e30f0a316,0x7fe9e76cdc8d7a0f00b3,0xf7490114ee10ac10cef8,0xb46769175ed13da511db,0xdb36e2f65036e829697e,0x6e9cf353c75efa384060,0x1b662103d2b94f239f3e,0x6479961c6845b1660087,0x30cd11700b1600d916f2,0x11e684f0b9f821d8dbd3,0x911ebcb824453d8cf0a5,0x90910990910990910990,0x3102903102903102909,0xb11390b11390b1031029,0x90a10a90a11390b11390,0x790690a90a10a90a10a,0x89079069079069079069,0x91892b91892b91892b91,0x8180f38108088000eb2b,0x11019011019011828820,0x204905a0490190110190],
[0x4103106204905a04906,0xba041031041031041031,0xb0730a30ba0db05307b0,0x84802284002a03b02221,0x183800100a00185002a,0xa05906205985800100a0,0x5104114a05906205914,0xca051041051041051041,0xb0b311b1ca12306b0e31,0x87003986803904b03919,0x1203300b023012878039,0xa00a0a200288001b02b0,0x910690aa00a0a20020a,0xb1091069091069091069,0x20b105a0b10620b105a0,0x3b01b08302303301306,0x8a89009a07308a8a002b,0x90810990818a809a8980,0x7a05a09908109908109,0xa90a207207a05a0a2072,0xa0a90120a901a0a90120,0x6100906100906100901,0x390ba039052039061009,0xb0230330b20ba0390520],
[0x8b80038d802b0430b206,0x628e08d08c808b8c0093,0x4b004d085b0043002f00,0x300c700010056004a00,0x2000700c80013000500,0x9888c780771a60e8200,0xb909d4b0c68c28ba1c7c,0x52c13ed7d73715e08324,0x9100ecaedce9d329d520,0xde2e6719d16871f6bbe6,0x26b29426e22ea92c2391,0x2d0651b1e2516db0ae4d,0xda2155fbc59ef3603fcb,0x14a5b4790330ae33a487,0x5b99cbe6c891620af679,0x986833454277a8b00a34,0x6c62961e6013c09acc1c,0xc2631a8eb1a5c76674f0,0x547e3b788247c54ce09c,0xc309010e668b28660183,0x996a30a22a7e9ccfc090,0x22084cdc8f0aeb6cdeb1,0xd3d6cc9bf9ee968cccad,0x30a3d887a62e18bd37cb],
[0x3abd942710ba12626b0f,0x96ba9a0ea1d6ac1d618a,0xbeb818725d4bf0a1511a,0x23571a358a985a866b5,0xfcc3f69b02b7c181cb26,0x40ade4d2577939b5e88,0x6704406252e50d913f2c,0x682d81d1e31e1ab5202b,0x22af8a0f7ad6473cb14a,0x774510b382b32c89be95,0x30da18d1a4e3873cc816,0x66cf1cb861223762eab9,0x2058142f94e21963d300,0xec6d6216a04ec71164aa,0x75124c39f9615054dae1,0xab07658db892cc0604f2,0xa5826ac74018430e4f2b,0x562b244af5d0e8c51fbb,0x1e098f40463303005906,0x432dcfaec200d4ca8442,0x89a76627bfa1e4011ae1,0x1b0c4b1e03cd8a89629d,0x26f13dfc984084dbe414,0xc442da4074a95738a297],
[0x73aef130084a99732516,0xcae4ed2584c4af17221,0x1300afe5e6a09b227ac5,0xa76e4a002112b60c98aa,0xb82467068b2df78b4a28,0x242400703bdc20633bc1,0x104c26d47d3a0224d038,0x30984c26130984caa130,0x6130984c26130984c041,0x536130983426130984d3,0x954261309a6c26130995,0x2184c261301094395009,0x130984c26dd7f1542613,0x2c5eae4419d005104c26,0x976242184da8e712935,0x19809e966ebb532dd353,0xf4d871ba13a5a5886134,0x6e38a09026134e070274,0x506ae4b13c26830e29c2,0x95b123e0984c26582504,0xba626dc723ac34207a95,0x9b0e2211cb2bee0a6181,0xba426b87938905708490,0xf93a4b24e1d138e4d259],
[0x32c2fca4513f5653985d,0x806c4f3eccb2272b4478,0x83e71a6f13501b87b3d8,0xd912958a715a97b1802c,0x84c26130984c26130984,0x561d558130984c261309,0x130984c64fb099154ac0,0x26130984c26130984c26,0x9f20edca3a2fc4469d68,0x2cf84632591c31d989f0,0xfcf49aab4c940ba4d3d4,0xba381cae269e0dc233b3,0x9160298aace38dbcd0f2,0x9ba2f9a92d95d27f2dcd,0x9de7242fa9e466cd2480,0x1321892d01301495f06b,0x26130984c26130984c26,0x4c26130984c26130984c,0x1cbf356ac204c2613098,0x30984c2613098aa54010,0x6130984c26130984c261,0xc26130984c26130984c2,0x84c26130984c26130984,0x984c26130984c261309],
[0x130984c26130984c2613,0x26130984c26130984c26,0x4c26130984c26130984c,0x984c26130985c2613218,0x30984c26130984c26130,0x6130984c26130984c261,0xc26130984c26130984c2,0x84c26130984c26130984,0x984c26130984c261309,0x130984c26130984c2613,0x26130984c26130984c26,0x4c26130984c26130984c,0x984c26130984c2613098,0x30984c26130984c26130,0xe135dd105e130984c261,0xc2613451d02613c68c58,0x67c26130984c26130984,0x4d84c265c3936026d7a5,0x130984c26130984c276f,0x50e6b726e9f842a84c26,0x4c26130984c27424d84d,0x9e7a138a0984c2613098,0x3099fce94061969f2300,0x9410984c261309c1426e],
[0xc69689e512c831a1de28,0x84c2613aca6c2613c6b0,0x5ee2126bc9e42ea00e09,0x3db884c276aa55a1b686,0x4c64a95b5be130984c26,0x4d0c9871e11f7533b1e0,0xa54adc130984c8a540a0,0xf3a84e58cdba04c2f15a,0x61309a62dc4009bef0e0,0x4ed41a8a3c6aafbebf82,0x2f9361309cda83597533,0x671bc16750984c261320,0x640ba558a0f68c6d6a13,0xfc134d84c2613755acbb,0x4c265394d887d6282152,0x984c26130984c26134d8,0x5b4d71f068af3a826130,0x6130984c1f690a04e12b,0x1033ea884c26130984c2,0x84c261309a5a86915302,0x5384c26130984c261309,0xda09caa8b18a8236f67f,0x26139ca6c26130150294,0x328cac7255c3ef7b884c],
[0x984c261355509367849d,0xa6f5ec26130984c26130,0x77ebc31c2607b60c1ae1,0x426130984c26130984c2,0x50b3d91bf0d58cc47862,0x984c26130984c8d8a18,0xd58f08a000f4ae102613,0x83dcfd2e66a818c257a,0x323b9d67610261309b3b,0xc04ef3e7dbee0590913,0xb3a04c26130f31ac4137,0x508639ccb6e5ba3f3111,0x9c6137180cd0133158f3,0xbe8f467128fe28130989,0x6c04db197b4aac153133,0x1816c02ac2b9ad947e61,0x66a9729ea3813381399f,0x4c9cdd09b751afa3d4bd,0xa241c22d09d94820aca0,0x37e27d9114804bd46130,0x22d1c04d9c3dd04c06e1,0xc10cc21b845b300984da,0x4e01140984cf83f8a2c,0x6845026137884c26ec95],
[0x1b0984c276bb204c2760,0x26f00984c26138b04d7f,0xdc32434b03026130984c,0x20220fb94d,0x2045840000000101,0x51200000000044150000,0x555000000000,0x44442000000020411,0x11112000001200221100,0x15000043400444000040,0x542118010000514400,0x51100010042111400,0x51000141015112000101,0x2000020000001551100,0x2200020011002200,0x221124161000210,0x45170433400040451d4,0x477c0400045514445400,0x540001544000455,0x10020452040010000120,0x100100110111000100,0x22001111110511001105,0x1115450f440011112200,0x20511500115401110000],
[0x1458000505001410,0x20200100000020048000,0x402000222112002100,0x44004000080044002224,0x410020c0c00040710441,0x22002000440000015000,0x51004440055500004404,0x44451040000044411114,0x1051000450244552200,0x10005002649000004540,0x55555500000054500c40,0x44044000640000610000,0x10010001100011007044,0x1404450530100454000,0x55034501015144445501,0x11010588100511010314,0x11111110020110001500,0x11405101111144000401,0x11511200000011215,0x22110000000118901110,0x211410014110510a8801,0x11014514451204014510,0x51011100150150100500,0x40110201811110111101],
[0x81020000100a20019101,0x11111000200002200,0x20022002000222000202,0x2020150401104020022,0x2222040040202022202,0x11124402100020454602,0x55021140111000021102,0x20825040400220005155,0x22240002220240040402,0x24161501044022246,0x51100441000244414445,0x24500402551141515502,0x4004415154402a04a,0x4114044020400505000,0x55154004044440544404,0x4041012051004040514,0x12814410100411021110,0x10200104400044044404,0x44044100441004044044,0x44000440240442011017,0x74c01504440400040404,0x40044500774144044444,0x45900222200445244400,0x15000004480155854004],
[0x2045021110454045015,0x51515555110451101151,0x4c044404550115111204,0x40045526411000045507,0x44041544440474544444,0x244005480512110405,0x5405546444c400055444,0x80045404450554815051,0x12007771410500005,0x22080450800418080041,0x40000425440811002122,0x45505508902004584008,0x11100005404000100002,0x1111100111001005400,0x50444010041110002010,0x40100820110458100444,0x11100104001010404404,0x20001410112054501110,0x41102441021410101222,0x44445244451044040111,0x44540010444811141510,0x4105000002000104554,0x1245111100001020,0x121111000120201211],
[0x10110111110000110101,0x1518111511101191011,0x10420011021002650511,0x1110501018001110440,0x11000011151110110400,0x15511111110001002211,0x111115511115111111,0x12000225421111504110,0x10002211204402045511,0x4114112445504112200,0x44551555541144410005,0x100011445914008111,0x15115041050000115000,0x54054541511151011110,0x20002211544515545111,0x50120944001512120222,0x44514084521214004445,0x19107013355504000212,0x1400d4474041140016,0x11104011201410514150,0x4510214400566550014,0x4145400000411144440,0x55555540041455110440,0x51510115000410020414],
[0x10152241504110151111,0x40445500401524441061,0x55550015444445421115,0x21155110440000155100,0x4040004071554810555,0x20200177cc002000017,0x201c004440141d191111,0x40280042000002222,0x200420000404401020,0x4200400644014200020,0x10222220002010004800,0x15015120110051100420,0x201115551111201114,0x40805445502020400161,0x15501120414100110020,0x220022200000205115,0x11020110442210000000,0x24044222111221102022,0x22222222200444222220,0x25115100152222222220,0x14044022450004420022,0x1240150500001225100,0x400222a0202404402200,0x45550224440244502024]]

def tile30 : List (List Nat) :=
[[0x55254405845500245500,0x92244020042600011004,0x12230073310443126,0x62400005444012400004,0x404000224000212222,0x40000140004045550040,0x40400080044022400044,0x1801501154000cd4c40,0x12040040024194444040,0x44400444424444400411,0x11100010054010000007,0x200040115000251140,0x14404004222222402012,0x44440444544042444444,0x744040444510011440,0x44404454005147404447,0x55151555404055021145,0x12441541004411844540,0x1410400015045410115,0x11151100014110001004,0x54150441140400545041,0x44415504511144415015,0xa0504440524188551141,0x112243033114101542],
[0x440000551445440000,0x400054444400011110,0x50444444004004144044,0x55440055000000440044,0x4044740044404044015,0x40005144044541141144,0x20441444440444441144,0x25004044444420454012,0x77044044400440040044,0x45444008801051444004,0x40244510444440121148,0x45004444404445004444,0x45444144440100444104,0x44044511114442444124,0x24010244440644400444,0x44444441554444444440,0x44440202014444440025,0x44444044444444041544,0x4444444504444444444,0x45440204664445114500,0x40400644501005001044,0x10445440450220445114,0x8a105055544458521554,0x11045044911150084144],
[0x44450044502444450005,0x2659004584502444444,0x594444450a2554000545,0x45451105512045451004,0x12220122414512054506,0x11110545124451044545,0x51454024600111454001,0x5500004c004544054418,0x40044145550d54407445,0x14455551111115455540,0x44502440224589525115,0x400515474d0444410047,0x482444540804477017,0x552200005000111510,0x11044450006508515550,0x50500200100240500115,0x10000000405004441004,0x1145150104450220050,0x10502115121511501141,0x40100000775040088001,0x35400450420519110450,0x54504511044110504400,0x409010225055454c44,0x22245551004544045051],
[0x10510111044100510110,0x4440044405101415110,0xc3205051044404440251,0x40511000116001510473,0x11041451515111012014,0x10045151120040444551,0x55515400221110512244,0x1615551555155555514,0x10000054010045000052,0x15540212122210540140,0x15554555115413007345,0x5000054254001144454,0x10544005400000544001,0x45144449005444444454,0x45514154580055455454,0x5154c051773455546554,0x455001195500110004,0x4000c055008444204455,0x40551011011511550440,0x11151120025510155104,0x4a510055221510014155,0x1555110551450554025,0x51151444455551141110,0x52005055555515055455],
[0x5755110c0440556055,0x10545515455840004440,0x412265111100111059,0x12744411111802737005,0x14103714447444551011,0x45007f300440011075,0x81804440026500804440,0x15244400118104400041,0x4040081545801455081,0x84845004444451842081,0x44501100008540550142,0x4511490044520551288,0x1951111554000902251,0x7447441004aa0002a000,0x440154c501114541ccc0,0xfffccf3145503ff01544,0x6ff7f5555fbff7f76def,0xdffffffffffffbeefddd,0x7ffffffffd7fffffffff,0xffffddffffffdfafeff7,0xfffdfffff5ffffbb7fff,0x2ffafffaf5dfff]]

def tiles (block : Nat) : List (List Nat) :=
  (if block < 15 then (if block < 7 then (if block < 3 then (if block < 1 then tile0 else (if block < 2 then tile1 else tile2)) else (if block < 5 then (if block < 4 then tile3 else tile4) else (if block < 6 then tile5 else tile6))) else (if block < 11 then (if block < 9 then (if block < 8 then tile7 else tile8) else (if block < 10 then tile9 else tile10)) else (if block < 13 then (if block < 12 then tile11 else tile12) else (if block < 14 then tile13 else tile14)))) else (if block < 23 then (if block < 19 then (if block < 17 then (if block < 16 then tile15 else tile16) else (if block < 18 then tile17 else tile18)) else (if block < 21 then (if block < 20 then tile19 else tile20) else (if block < 22 then tile21 else tile22))) else (if block < 27 then (if block < 25 then (if block < 24 then tile23 else tile24) else (if block < 26 then tile25 else tile26)) else (if block < 29 then (if block < 28 then tile27 else tile28) else (if block < 30 then tile29 else tile30)))))

def dataWord (i : Nat) : Nat :=
  strict i fun j => ((tiles (j/384)).getD ((j/24) % 16) []).getD (j % 24) 0

def directFamilyAt : Nat := 0
def directSegmentsAt : Nat := 198
def directFeaturesAt : Nat := 3874
def directNumbersAt : Nat := 5215
def paletteFamilyAt : Nat := 12253
def paletteIndexAt : Nat := 12451
def paletteValuesAt : Nat := 16714
def cdfAt : Nat := 32529
def distributionsAt : Nat := 35936
def proofsAt : Nat := 36244
def casesAt : Nat := 104516
def blocksAt : Nat := 105902
def claimsAt : Nat := 108912
def claimWordsAt : Nat := 111739
def claimSpecialsAt : Nat := 112099
def groupWidth : Nat := 8
def spanBits : Nat := 6
def beginBits : Nat := 14
def region (v : Nat) : Nat × Nat :=
  (if v < 4028 then (if v < 1510 then (if v < 1080 then (if v < 550 then (if v < 50 then (0,0) else (1,50)) else (if v < 1050 then (2,550) else (3,1050))) else (if v < 1480 then (if v < 1180 then (4,1080) else (5,1180)) else (if v < 1500 then (6,1480) else (7,1500)))) else (if v < 3390 then (if v < 1940 then (if v < 1660 then (8,1510) else (9,1660)) else (if v < 3340 then (10,1940) else (11,3340))) else (if v < 3636 then (if v < 3440 then (12,3390) else (13,3440)) else (if v < 3832 then (14,3636) else (15,3832))))) else (if v < 6856 then (if v < 5288 then (if v < 4924 then (if v < 4224 then (16,4028) else (17,4224)) else (if v < 4938 then (18,4924) else (19,4938))) else (if v < 6688 then (if v < 5988 then (20,5288) else (21,5988)) else (if v < 6716 then (22,6688) else (23,6716)))) else (if v < 9118 then (if v < 7998 then (if v < 7742 then (24,6856) else (25,7742)) else (if v < 8798 then (26,7998) else (27,8798))) else (if v < 11230 then (if v < 10014 then (28,9118) else (29,10014)) else (if v < 13730 then (30,11230) else (if v < 16230 then (31,13730) else (32,16230)))))))
def contextIndex (ctx : Nat) : Nat :=
  (if ctx < 900 then (if ctx < 48 then (0+ctx-0) else (if ctx < 600 then (38+ctx-48) else (46+ctx-600))) else (if ctx < 1000 then (57+ctx-900) else (if ctx < 1150 then (59+ctx-1000) else (73+ctx-1150))))
def bitWindow (position count : Nat) : Nat :=
  if count=0 then 0 else strict position fun start => strict count fun width =>
  let q := start / 80
  let s := start % 80
  let lo := dataWord q >>> s
  let mid := if 80 < s+width then lo ||| (dataWord (q+1) <<< (80-s)) else lo
  let full := if 160 < s+width then mid ||| (dataWord (q+2) <<< (160-s)) else mid
  full &&& ((1 <<< width)-1)

def little (p n : Nat) := bitWindow (8*p) (8*n)
def byte (p : Nat) := little p 1

def lowBitNumber (n : Nat) := Nat.log2 (n ^^^ (n &&& (n-1)))

def readGamma (p : Nat) : Nat × Nat :=
  strict p fun position =>
  let width := lowBitNumber (bitWindow position 20)
  ((1 <<< width) + bitWindow (position+width+1) width,position+2*width+1)

def piece (n start width : Nat) := (n >>> start) &&& ((1 <<< width)-1)

def boundaryStart : Nat := 0
def boundaryWidth : Nat := 10
def tagStart : Nat := 10
def tagWidth : Nat := 8
def signStart : Nat := 18
def signWidth : Nat := 22
def factorStart : Nat := 40
def factorWidth : Nat := 13
def numberWidthStart : Nat := 53
def numberWidthWidth : Nat := 6
def numberStartStart : Nat := 59
def numberStartWidth : Nat := 16
def termStartStart : Nat := 75
def termStartWidth : Nat := 9
def termCountStart : Nat := 84
def termCountWidth : Nat := 3
def segmentWidth : Nat := 87
def featureDivStart : Nat := 0
def featureDivWidth : Nat := 10
def featureModStart : Nat := 10
def featureModWidth : Nat := 7
def featureWeightStart : Nat := 17
def featureWeightWidth : Nat := 16
def featureWidth : Nat := 33

def selectBit (base : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0,_,position,_ => position
  | fuel+1,rank,position,word =>
    if word=0 then
      strict (bitWindow (base+position+64) 64) fun more => selectBit base fuel rank (position+64) more
    else if rank=0 then position+lowBitNumber word
    else selectBit base fuel (rank-1) position (word &&& (word-1))

def monotoneAt (start low count index : Nat) : Nat :=
  strict count fun n => strict index fun j =>
  let w := Nat.log2 (3*n)+1
  let q := j/16
  let checks := start+n*low
  strict (if q=0 then 0 else bitWindow (checks+(q-1)*w) w) fun before =>
  let highs := checks+((n-1)/16)*w
  strict (bitWindow (highs+before) 64) fun word =>
  let position := selectBit highs (n+21) (j % 16) before word
  ((position-j) <<< low)+bitWindow (start+j*low) low

def selectSegment (ordinal : Nat) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | k+1,lo,hi =>
    if hi-lo≤1 then lo else
      let pivot := (lo+hi)/2
      let previous := bitWindow (8*directSegmentsAt+segmentWidth*(pivot-1)) boundaryWidth
      if ordinal < previous then selectSegment ordinal k lo pivot else selectSegment ordinal k pivot hi

def linearFeature (coord : Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0,_,pos,neg => (pos,neg)
  | n+1,index,pos,neg =>
    strict (bitWindow (8*directFeaturesAt+featureWidth*index) featureWidth) fun row =>
    let divisor := piece row featureDivStart featureDivWidth
    let modulus := piece row featureModStart featureModWidth
    let signedWeight := piece row featureWeightStart featureWeightWidth
    let digit := coord/divisor
    let v := if modulus=0 then digit else digit % modulus
    if signedWeight % 2 = 0 then linearFeature coord n (index+1) (pos+v*(signedWeight/2)) neg
    else linearFeature coord n (index+1) pos (neg+v*(signedWeight/2+1))

def templateAt (f coord index : Nat) : Nat :=
  strict index fun ordinal =>
  strict (little (directFamilyAt+3*f) 3) fun fam =>
  let first := fam &&& 65535
  let total := fam >>> 16
  strict (selectSegment ordinal 12 first (first+total)) fun j =>
  strict (bitWindow (8*directSegmentsAt+segmentWidth*j) segmentWidth) fun desc =>
  let code := piece desc tagStart tagWidth
  if code<2 then code else
    let old := if j=first then 0 else bitWindow (8*directSegmentsAt+segmentWidth*(j-1)) boundaryWidth
    let within := ordinal-old
    let w := piece desc numberWidthStart numberWidthWidth
    let start := piece desc numberStartStart numberStartWidth
    let value := if w=0 then within else if w<32 then bitWindow (8*directNumbersAt+start+w*within) w
      else monotoneAt (8*directNumbersAt+start) (w-32) (piece desc boundaryStart boundaryWidth-old) within
    let base := piece desc signStart signWidth
    let magnitude := piece desc factorStart factorWidth
    let pos := value*magnitude+(if base % 2 = 0 then base/2 else 0)
    let neg := if base % 2 = 0 then 0 else base/2+1
    let (plus,minus) := linearFeature coord (piece desc termCountStart termCountWidth) (piece desc termStartStart termStartWidth) pos neg
    if plus<minus then 2 else 3+(code-2)+128*(plus-minus)

def sumPacked (word : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => sumPacked word j + piece word (spanBits*j) spanBits

abbrev Menu := Nat × Nat × Nat × Nat × Nat

def menuFor (p : Nat) : Menu :=
  strict p fun id =>
  let v := id/2
  let (shape,origin) := region v
  let coord := v-origin
  let family := 2*shape+(id % 2)
  strict (little (paletteFamilyAt+3*family) 3) fun dir =>
  let base := dir &&& 65535
  let width := dir >>> 16
  let g := coord/groupWidth
  let block := base+g/16
  let entry := 8*paletteIndexAt+(beginBits+16*spanBits)*block
  strict (bitWindow (entry+beginBits) (16*spanBits)) fun lengths =>
  let j := g % 16
  if piece lengths (spanBits*j) spanBits = 0 then (family,coord,0,0,width) else
    let start := bitWindow entry beginBits + sumPacked lengths j
    let (n,pos) := readGamma (8*(paletteValuesAt+start))
    (family,coord,n,pos,width)

def tailOrdinal : Nat → Nat → Nat → Nat
  | 0,p,base => base + (readGamma p).1 - 1
  | j+1,p,base =>
    let (gap,next) := readGamma p
    tailOrdinal j next (base+gap)

def optionAt (m : Menu) (i : Nat) : Nat :=
  let (f,x,n,p,w) := m
  if i≥n then 2 else
    let t := if i<3 then bitWindow (p+i*w) w else tailOrdinal (i-3) (p+3*w) 0
    templateAt f x t

def optionCount (m : Menu) : Nat := m.2.2.1

def optionsFor (p : Nat) := let m := menuFor p; (List.range (optionCount m)).map (optionAt m)
def distLow (start s : Nat) := if s=0 then 0 else bitWindow (8*cdfAt+12*(start+s-1)) 12

def searchDistribution (start pos : Nat) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | k+1,lo,hi =>
    if hi-lo≤1 then lo else
      let pivot := (lo+hi)/2
      if distLow start pivot ≤ pos then searchDistribution start pos k pivot hi
      else searchDistribution start pos k lo pivot

def interval (context residue : Nat) : Nat × Nat × Nat :=
  strict context fun ctx => strict residue fun pos =>
  let id := contextIndex ctx
  let row := little (distributionsAt+4*id) 4
  let start := row/512
  let last := row % 512
  let symbol := searchDistribution start pos 12 0 (last+1)
  let lo := distLow start symbol
  let hi := if symbol=last then 4096 else distLow start (symbol+1)
  (symbol,lo,hi-lo)

def digitBits : Nat := 4
def cacheOn : Bool := true
def headerFamily (t : Nat) : Nat :=
  match t with
  | 11 => 1
  | 12 => 2
  | 128 => 3
  | _ => 0
def claimRoot (k : Nat) : Nat := match k with
  | 0 => 48
  | 1 => 96
  | 2 => 136
  | 3 => 176
  | _ => 232

def claimCode : Nat → Nat → Nat → Nat → Nat × Nat
  | 0,_,_,p => (0,p)
  | n+1,start,look,p =>
    strict (bitWindow (8*claimWordsAt+12*(start+(look &&& 7))) 12) fun item =>
    if item<2048 then (item/8,p+item % 8)
    else claimCode n (item-2048) (look >>> 3) (p+3)

def claimNumber (context position : Nat) : Nat × Nat :=
  strict position fun p =>
  let (s,after) := claimCode 4 (claimRoot context) (bitWindow p 9) p
  if context<3 then (s,after)
  else if s<8 then (little (claimSpecialsAt+2*((context-3)*8+s)) 2,after)
  else let width := s-8
       ((1 <<< width)-1+bitWindow after width,after+width)
end PriorG11.Compressed

namespace PriorG11.Learning

abbrev Lit := Nat × Bool
abbrev Clause := List Lit

def opposite (l : Lit) : Lit := (l.1,!l.2)
def agrees (v : Nat → Bool) (l : Lit) : Prop := v l.1 = l.2
def holds (v : Nat → Bool) (c : Clause) : Prop := ∃ l ∈ c, agrees v l
theorem opposite_agrees (v : Nat → Bool) (l : Lit) : agrees v (opposite l) ↔ ¬agrees v l := by
  simp only [agrees,opposite]
  cases v l.1 <;> cases l.2 <;> decide

def tag (l : Lit) := 2*l.1+l.2.toNat
def assign (a : Nat) (l : Lit) : Nat := a ||| (1 <<< tag l)
def respects (v : Nat → Bool) (a : Nat) : Prop := ∀ l, a.testBit (tag l) = true → agrees v l

theorem tag_injective : Function.Injective tag := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  cases b <;> cases d <;> simp [tag,Bool.toNat] at h ⊢ <;> omega

theorem respects_add {v a p} (ha : respects v a) (hp : agrees v p) : respects v (assign a p) := by
  intro l hit
  have h : a.testBit (tag l)=true ∨ p=l := by
    simpa [assign,Nat.shiftLeft_eq,Nat.testBit_two_pow,tag_injective.eq_iff] using hit
  rcases h with old|rfl
  · exact ha _ old
  · exact hp

def allFalseExcept (a : Nat) (keep : Option Lit) (c : Clause) : Bool :=
  c.all fun l => some l == keep || a.testBit (tag (opposite l))

theorem surviving_literal {v c a keep} (hc : holds v c) (ha : respects v a)
    (test : allFalseExcept a keep c = true) : ∃ l, some l = keep ∧ agrees v l := by
  obtain ⟨l,mem,ok⟩ := hc
  have h := List.all_eq_true.mp test l mem
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  rcases h with same|neg
  · exact ⟨l,same,ok⟩
  · exact ((opposite_agrees v l).mp (ha _ neg) ok).elim

def evaluated {α : Type} (x : Nat) (f : Nat → α) : α :=
  match x with | 0 => f 0 | k+1 => f (k+1)

theorem evaluated_eq {α : Type} (x : Nat) (f : Nat → α) : evaluated x f = f x := by
  cases x <;> rfl

inductive Obligation where
  | need (fact : Lit)
  | finish (fact : Lit) (reason : Nat)

structure Trail (α : Type) where
  permanent : Nat
  conditional : Nat
  stream : α
  hypotheses : Clause

abbrev Picker (α : Type) := Nat → Nat → Lit → α → Option (Option (Nat × Bool) × α)

def Trail.valid {α : Type} (v : Nat → Bool) (s : Trail α) :=
  respects v s.permanent ∧ ((∀ p ∈ s.hypotheses, agrees v p) → respects v s.conditional)

def Trail.assertPermanent {α : Type} (s : Trail α) (p : Lit) : Trail α :=
  evaluated (assign s.permanent p) fun r =>
    evaluated (assign s.conditional p) fun a => ⟨r,a,s.stream,s.hypotheses⟩

def Trail.assertConditional {α : Type} (s : Trail α) (p : Lit) : Trail α :=
  evaluated (assign s.conditional p) fun a => ⟨s.permanent,a,s.stream,s.hypotheses⟩

def Trail.assume {α : Type} (s : Trail α) (p : Lit) (more : α) : Trail α :=
  evaluated (assign s.conditional p) fun a => ⟨s.permanent,a,more,p::s.hypotheses⟩

theorem Trail.assume_valid {α : Type} {v s p} (more : α) (h : Trail.valid v s) : Trail.valid v (s.assume p more) := by
  simp only [Trail.assume,evaluated_eq,Trail.valid]
  refine ⟨h.1,fun facts => respects_add (h.2 ?_) (facts _ List.mem_cons_self)⟩
  intro l hl
  exact facts l (List.mem_cons_of_mem p hl)

theorem forced {v r p c} (hc : holds v c) (hr : respects v r) (tested : allFalseExcept r (some p) c = true) :
    agrees v p := by
  obtain ⟨l,eq,hl⟩ := surviving_literal hc hr tested
  exact Option.some.inj eq ▸ hl

def needs (p : Lit) (c : Clause) : List Obligation :=
  (c.filter fun l => l != p).map fun l => .need (opposite l)

def walk {α : Type} (db : Nat → Clause) (pick : Picker α) :
    Nat → Trail α → List Obligation → Option (Trail α)
  | _,s,[] => some s
  | 0,_,_ :: _ => none
  | fuel+1,s,.need p :: tail =>
    if s.conditional.testBit (tag p) then walk db pick fuel s tail
    else match pick s.permanent s.conditional p s.stream with
      | none => none
      | some (none,more) => walk db pick fuel (s.assume p more) tail
      | some (some reason,more) =>
        let finish := .finish p reason.1 :: tail
        let next := if reason.2 then finish else needs p (db reason.1) ++ finish
        walk db pick fuel {s with stream := more} next
  | fuel+1,s,.finish p key :: tail =>
    if allFalseExcept s.permanent (some p) (db key) then
      walk db pick fuel (s.assertPermanent p) tail
    else if allFalseExcept s.conditional (some p) (db key) then
      walk db pick fuel (s.assertConditional p) tail
    else none

theorem walk_preserves {α : Type} {db : Nat → Clause} {pick : Picker α} {v fuel s t tasks}
    (hm : ∀ i, holds v (db i)) (valid : Trail.valid v s) (done : walk db pick fuel s tasks = some t) :
    Trail.valid v t := by
  induction fuel generalizing s tasks with
  | zero =>
    cases tasks with
    | nil => exact Option.some.inj done ▸ valid
    | cons h q => cases done
  | succ n ih =>
    cases tasks with
    | nil => exact Option.some.inj done ▸ valid
    | cons action tail =>
      cases action with
      | need p =>
        by_cases known : s.conditional.testBit (tag p)=true
        · exact ih valid (by simpa only [walk,if_pos known] using done)
        · cases h : pick s.permanent s.conditional p s.stream with
          | none => simp only [walk,if_neg known,h,reduceCtorEq] at done
          | some pair =>
            obtain ⟨ref,more⟩ := pair
            cases ref with
            | none => exact ih (Trail.assume_valid more valid) (by simpa only [walk,if_neg known,h] using done)
            | some key => exact ih (s := {s with stream := more}) valid (by simpa only [walk,if_neg known,h] using done)
      | finish p key =>
        by_cases perm : allFalseExcept s.permanent (some p) (db key)=true
        · have hp := forced (hm key) valid.1 perm
          have next : Trail.valid v (s.assertPermanent p) := by
            simp only [Trail.assertPermanent,evaluated_eq,Trail.valid]
            exact ⟨respects_add valid.1 hp,fun scope => respects_add (valid.2 scope) hp⟩
          exact ih next (by simpa only [walk,if_pos perm] using done)
        · by_cases cond : allFalseExcept s.conditional (some p) (db key)=true
          · have next : Trail.valid v (s.assertConditional p) := by
              simp only [Trail.assertConditional,evaluated_eq,Trail.valid]
              exact ⟨valid.1,fun scope => respects_add (valid.2 scope) (forced (hm key) (valid.2 scope) cond)⟩
            exact ih next (by simpa only [walk,if_neg perm,if_pos cond] using done)
          · simp only [walk,if_neg perm,if_neg cond,reduceCtorEq] at done

def insertLit (p : Lit) : Clause → Clause
  | [] => [p]
  | q::rest => if tag p ≤ tag q then p::q::rest else q::insertLit p rest

theorem mem_insertLit {l p c} (h : l=p ∨ l∈c) : l∈insertLit p c := by
  induction c with
  | nil => simpa [insertLit] using h
  | cons q t ih =>
    by_cases early : tag p ≤ tag q
    · simpa only [insertLit,if_pos early,List.mem_cons] using h
    · simp only [insertLit,if_neg early,List.mem_cons]
      rcases h with rfl|inc
      · exact Or.inr (ih (Or.inl rfl))
      · rcases List.mem_cons.mp inc with same|other
        · exact Or.inl same
        · exact Or.inr (ih (Or.inr other))

def sortLits : Clause → Clause
  | [] => []
  | p::rest => insertLit p (sortLits rest)

theorem mem_sortLits {l c} (h : l∈c) : l∈sortLits c := by
  induction c with
  | nil => cases h
  | cons p rest ih =>
    apply mem_insertLit
    exact (List.mem_cons.mp h).imp_right ih

def consequence (hyps additional : Clause) : Clause := sortLits (additional ++ hyps.map opposite)

theorem consequence_holds {v hyps additional} (notAll : ¬(∀ p ∈ hyps, agrees v p)) :
    holds v (consequence hyps additional) := by
  push Not at notAll
  obtain ⟨p,hp,bad⟩ := notAll
  have inc : opposite p ∈ additional ++ hyps.map opposite := List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  exact ⟨opposite p,mem_sortLits inc,(opposite_agrees v p).mpr bad⟩

abbrev Packet (α : Type) := Nat × Clause × α

def derive {α : Type} (db : Nat → Clause) (pick : Picker α) (fuel root : Nat)
    (packet : Packet α) : Option (Nat × Clause × α) :=
  let start : Trail α := ⟨root,root,packet.2.2,[]⟩
  let closing := db packet.1
  match walk db pick fuel start (closing.map fun l => .need (opposite l)) with
  | none => none
  | some final => if allFalseExcept final.conditional none closing then
      some (final.permanent,consequence final.hypotheses packet.2.1,final.stream) else none

theorem derive_sound {α : Type} {db : Nat → Clause} {pick : Picker α} {v root next clause cursor} {packet : Packet α} {fuel}
    (hm : ∀ i, holds v (db i)) (hr : respects v root) (ok : derive db pick fuel root packet = some (next,clause,cursor)) :
    respects v next ∧ holds v clause := by
  let start : Trail α := ⟨root,root,packet.2.2,[]⟩
  have hi : Trail.valid v start := ⟨hr,fun _ => hr⟩
  cases hw : walk db pick fuel start ((db packet.1).map fun l => .need (opposite l)) with
  | none => simp only [derive,show (⟨root,root,packet.2.2,[]⟩ : Trail α)=start from rfl,hw,reduceCtorEq] at ok
  | some final =>
    have sound := walk_preserves hm hi hw
    by_cases hit : allFalseExcept final.conditional none (db packet.1)=true
    · have eq : (final.permanent,consequence final.hypotheses packet.2.1,final.stream)=(next,clause,cursor) := by
        simpa only [derive,show (⟨root,root,packet.2.2,[]⟩ : Trail α)=start from rfl,hw,if_pos hit,Option.some.injEq] using ok
      have ec : consequence final.hypotheses packet.2.1 = clause := congrArg (fun p => p.2.1) eq
      have er : final.permanent = next := congrArg Prod.fst eq
      rw [← er,← ec]
      refine ⟨sound.1,consequence_holds ?_⟩
      intro hypotheses
      obtain ⟨p,absurd,_⟩ := surviving_literal (hm packet.1) (sound.2 hypotheses) hit
      cases absurd
    · simp only [derive,show (⟨root,root,packet.2.2,[]⟩ : Trail α)=start from rfl,hw,if_neg hit,reduceCtorEq] at ok

def tautology : Clause := [(0,false),(0,true)]

theorem holds_tautology (v : Nat → Bool) : holds v tautology := by
  cases h : v 0 with
  | false => exact ⟨(0,false),by decide,h⟩
  | true => exact ⟨(0,true),by decide,h⟩

def rule (source : Nat → Clause) (prior : List Clause) (n key : Nat) : Clause :=
  if key % 2=0 then source (key/2) else if key/2<n then prior.getD (n-1-key/2) tautology else tautology

theorem rule_holds {source v prior n} (hs : ∀ i, holds v (source i))
    (hd : ∀ c ∈ prior, holds v c) (key : Nat) : holds v (rule source prior n key) := by
  unfold rule
  split
  · exact hs _
  · split
    · rw [List.getD_eq_getElem?_getD]
      cases h : prior[n-1-key/2]? with
      | none => exact holds_tautology v
      | some c => exact hd c (List.mem_of_getElem? h)
    · exact holds_tautology v

abbrev Cursor := Nat
abbrev Distribution := Nat → Nat → Nat × Nat × Nat

def makeCursor (v pos : Nat) : Cursor := (pos <<< 32) ||| v

def refill (read : Nat → Nat) (v pos : Nat) : Cursor :=
  if v < 8388608 then
    evaluated (v*256+read pos) fun w =>
      if w < 8388608 then makeCursor (w*256+read (pos+1)) (pos+2) else makeCursor w (pos+1)
  else makeCursor v pos

def draw (read : Nat → Nat) (interval : Distribution) (ctx : Nat) (s : Cursor) : Nat × Cursor :=
  evaluated s fun word =>
    let residue := word &&& 4095
    let (symbol,lo,count) := interval ctx residue
    let next := count * ((word &&& 4294967295) >>> 12) + (residue-lo)
    (symbol,evaluated next fun v => refill read v (word >>> 32))

def rankOrOnly (read : Nat → Nat) (interval : Distribution) (count ctx : Nat) (s : Cursor) : Nat × Cursor :=
  if count ≤ 1 then (0,s) else draw read interval ctx s

def priorRefs (p : Lit) (n : Nat) : List Clause → List Nat
  | [] => []
  | c::cs => if p ∈ c then (2*(n-1)+1) :: priorRefs p (n-1) cs else priorRefs p (n-1) cs

end PriorG11.Learning

namespace PriorG11.Stream
open PriorG11.Learning
open PriorG11.Compressed

abbrev State := Nat × Nat

def symbol (ctx s : Nat) := draw byte interval ctx s

def digitNumber (ctx : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0,_,_,acc,s => (acc,s)
  | fuel+1,tier,shift,acc,s =>
    let (digit,after) := symbol (ctx+min 3 tier) s
    let base := 1 <<< digitBits
    let total := acc+((digit % base) <<< shift)
    if digit<base then (total,after) else digitNumber ctx fuel (tier+1) (shift+digitBits) total after

def transmittedNat (ctx s : Nat) := digitNumber ctx 8 0 0 0 s

def readExtras : Nat → Nat → Nat → Clause × Nat
  | 0,_,s => ([],s)
  | count+1,base,s =>
    let (gap,after) := transmittedNat 1150 s
    let v := base+gap
    let (rest,final) := readExtras count (v+1) after
    ((v/2,v % 2 == 1)::rest,final)

def packet (step : Nat) (s : State) : Packet State :=
  let (family,afterFamily) := symbol 900 s.1
  let (param,afterParam) := transmittedNat (1000+4*headerFamily family) afterFamily
  let closing := if family=128 then 2*(step-1-param)+1 else 2*(family+128*param)
  let (count,afterCount) := symbol 901 afterParam
  let (extra,after) := readExtras count 0 afterCount
  (closing,extra,(after,s.2))

def presentUnit (a : Nat) (p : Lit) : Bool → Clause → Bool
  | seen, [] => seen
  | seen, h :: tail => if h = p then presentUnit a p true tail
    else a.testBit (tag (opposite h)) && presentUnit a p seen tail

def firstForced (source : Nat → Clause) (enabled : Nat → Bool) (conditional : Nat) (p : Lit) (m : Menu) :
    Nat → Nat → Nat → Option Nat
  | 0,_,_ => none
  | _+1,_,0 => none
  | fuel+1,i,left+1 =>
    if i≥optionCount m then none else
      let a := optionAt m i
      if a<2 then firstForced source enabled conditional p m fuel (i+1) (left+1) else
        if 3≤a && presentUnit conditional p false (source (a-3)) then some a
        else firstForced source enabled conditional p m fuel (i+1) left

def literalMode (id : Nat) : Nat :=
  strict id fun i =>
    let index := bitWindow (897048+9*(i/24)) 9
    bitWindow (910344+48*index+2*(i % 24)) 2

def useHints (cell : Nat) := bitWindow (930552+cell) 1 == 1

def guidedChoice (i : Nat) : Nat :=
  (if i<1829 then (if i<818 then (if i<614 then (if i<418 then (if i<88 then (if i<84 then 135297 else (if i<86 then 135425 else 135425)) else (if i<99 then (if i<94 then 135441 else 135553) else (if i<416 then 433881 else 77825))) else (if i<512 then (if i<436 then (if i<430 then 77953 else 1059777) else (if i<437 then 222465 else 221249)) else (if i<537 then (if i<519 then 77569 else 78017) else (if i<559 then 117569 else 124097)))) else (if i<730 then (if i<708 then (if i<626 then 84097 else (if i<637 then 142745 else 158465)) else (if i<716 then (if i<714 then 83713 else 84097) else (if i<728 then 84225 else 144153))) else (if i<810 then (if i<754 then (if i<736 then 1089873 else 146969) else (if i<808 then 1090001 else 77313)) else (if i<816 then (if i<812 then 77441 else 77569) else (if i<817 then 77825 else 77905))))) else (if i<924 then (if i<839 then (if i<833 then (if i<830 then 77969 else (if i<832 then 96641 else 238865)) else (if i<837 then (if i<835 then 122449 else 122561) else (if i<838 then 161025 else 230273))) else (if i<859 then (if i<848 then (if i<846 then 52353 else 1102817) else (if i<850 then 1102785 else 1102817)) else (if i<908 then (if i<906 then 161153 else 70785) else (if i<910 then 70913 else 71041)))) else (if i<1028 then (if i<937 then (if i<930 then 141825 else (if i<935 then 145689 else 187777)) else (if i<959 then (if i<939 then 5337 else 61313) else (if i<1017 then 162433 else 71489))) else (if i<1416 then (if i<1048 then (if i<1036 then 102913 else 84225) else (if i<1056 then 102913 else 414401)) else (if i<1639 then (if i<1436 then 89793 else 239105) else (if i<1737 then 322113 else 329153)))))) else (if i<5258 then (if i<4613 then (if i<2239 then (if i<1935 then (if i<1929 then 393793 else (if i<1933 then 400833 else 420033)) else (if i<2108 then (if i<2106 then 426433 else 160481) else (if i<2235 then 160609 else 134849))) else (if i<2538 then (if i<2277 then (if i<2257 then 28129 else 34393) else (if i<2466 then 135489 else 134865)) else (if i<2856 then (if i<2696 then 135633 else 136785) else (if i<2956 then 138065 else 138065)))) else (if i<5036 then (if i<4822 then (if i<4614 then 221896 else (if i<4616 then 2193 else 2321)) else (if i<4826 then (if i<4823 then 242817 else 224584) else (if i<5033 then 2961 else 227272))) else (if i<5252 then (if i<5146 then (if i<5143 then 3601 else 228680) else (if i<5250 then 4241 else 116225)) else (if i<5254 then (if i<5253 then 117529 else 230088) else (if i<5256 then 4753 else 4881))))) else (if i<6770 then (if i<6563 then (if i<6470 then (if i<6153 then 5009 else (if i<6156 then 241608 else 4881)) else (if i<6476 then (if i<6472 then 128641 else 129945) else (if i<6560 then 6161 else 122393))) else (if i<6665 then (if i<6566 then (if i<6564 then 246856 else 5393) else (if i<6663 then 5521 else 248136)) else (if i<6668 then (if i<6666 then 248136 else 5521) else (if i<6756 then 5649 else 4881)))) else (if i<17242 then (if i<7242 then (if i<6772 then 414169 else (if i<6778 then 414297 else 6289)) else (if i<16788 then (if i<16782 then 228761 else 2961) else (if i<17240 then 34521 else 4753))) else (if i<30646 then (if i<17410 then (if i<17408 then 4881 else 60121) else (if i<29636 then 5393 else 4881)) else (if i<31636 then (if i<31606 then 5521 else 2961) else (if i<32676 then 4881 else 433041)))))))

def suggested (hinted : Bool) (source : Nat → Clause) (enabled : Nat → Bool)
    (a : Nat) (p : Lit) (menu : Menu) : Option Nat :=
  let stored := if hinted then literalMode (tag p) else 0
  let mode := if stored=3 then strict (guidedChoice (tag p)) fun word =>
      if a.testBit (word >>> 6) then (word >>> 3) &&& 7 else word &&& 7
    else stored
  if mode=0 then firstForced source enabled a p menu 4 0 2
  else if mode=1 then none else
    let code := optionAt menu (mode-2)
    if 3≤code then some code else none

def chooseReason (hinted : Bool) (source : Nat → Clause) (enabled : Nat → Bool) (n : Nat) (prior : List Clause)
    (_root conditional : Nat) (p : Lit) (s : State) : Option (Option (Nat × Bool) × State) :=
  let id := tag p
  let m := evaluated id menuFor
  match suggested hinted source enabled conditional p m with
  | some a => some (some (2*(a-3),true),s)
  | none =>
    let size := optionCount m
    let shift := 24*(((id*1103515245+12345) >>> 11) % 512)
    let old := if cacheOn then (s.2 >>> shift) &&& 16777215 else 0
    let reuse := cacheOn && size>1 && old/128==id+1
    let (value,after) := rankOrOnly byte interval size (2*((size-1)/3)+reuse.toNat) s.1
    let rank := if reuse then if value=0 then old % 128 else if value-1 < old % 128 then value-1 else value else value
    let saved := if cacheOn && size>1 then s.2 ^^^ ((old ^^^ ((id+1)*128+rank)) <<< shift) else s.2
    if rank≥size then none else match optionAt m rank with
    | 0 => some (none,(after,saved))
    | 1 =>
      let refs := priorRefs p n prior
      let (which,more) := rankOrOnly byte interval refs.length (600+(refs.length-1)/3) after
      (refs[which]?).map fun key => (some (key,false),(more,saved))
    | 2 => none
    | a+3 => some (some (2*a,false),(after,saved))

end PriorG11.Stream
namespace PriorG11.Blocks
open PriorG11.Learning PriorG11.Stream

abbrev Claims := List (Nat × Clause)

def preserves (v : Nat → Bool) (outputs : Claims) := ∀ item ∈ outputs, holds v item.2

def validate (step : Nat) (c : Clause) : Claims → Option Claims
  | [] => some []
  | x::xs => if x.1 = step then (if x.2 = c then some xs else none) else some (x::xs)

theorem validate_correct {step c outputs rest v} (hc : holds v c)
    (checked : validate step c outputs = some rest) (ok : preserves v rest) : preserves v outputs := by
  cases outputs with
  | nil => intro a h; cases h
  | cons x xs =>
    by_cases hi : x.1 = step
    · by_cases equal : x.2 = c
      · have e : xs = rest := by simpa only [validate,if_pos hi,if_pos equal,Option.some.injEq] using checked
        intro a member
        rcases List.mem_cons.mp member with rfl|old
        · exact equal ▸ hc
        · exact ok a (e ▸ old)
      · simp only [validate,if_pos hi,if_neg equal,reduceCtorEq] at checked
    · have e : x::xs = rest := by simpa only [validate,if_neg hi,Option.some.injEq] using checked
      exact e ▸ ok

def segment {α : Type} (source : Nat → Clause) (pick : Nat → List Clause → Picker α)
    (packet : Nat → α → Packet α) (fuel : Nat) : Nat → Nat → Nat → Nat → List Clause → α → Claims → Bool
  | 0,_,_,_,_,_,outputs => outputs.isEmpty
  | k+1,step,n,root,prior,input,outputs =>
    match derive (rule source prior n) (pick n prior) fuel root (packet n input) with
    | none => false
    | some (next,clause,after) =>
      match validate step clause outputs with
      | none => false
      | some rest => evaluated next fun r =>
        segment source pick packet fuel k (step+1) (n+1) r (clause::prior) after rest

theorem segment_sound {α : Type} {source : Nat → Clause} {pick : Nat → List Clause → Picker α}
    {packet : Nat → α → Packet α} {v fuel k} (hs : ∀ i, holds v (source i))
    {step n root prior input outputs} (hp : ∀ c ∈ prior, holds v c) (hr : respects v root)
    (ok : segment source pick packet fuel k step n root prior input outputs=true) : preserves v outputs := by
  induction k generalizing step n root prior input outputs with
  | zero =>
    cases outputs with
    | nil => intro o h; cases h
    | cons o os => cases ok
  | succ k ih =>
    cases hd : derive (rule source prior n) (pick n prior) fuel root (packet n input) with
    | none => simp only [segment,hd,reduceCtorEq] at ok
    | some result =>
      obtain ⟨next,c,after⟩ := result
      obtain ⟨hn,hc⟩ := derive_sound (rule_holds hs hp) hr hd
      cases hval : validate step c outputs with
      | none => simp only [segment,hd,hval,reduceCtorEq] at ok
      | some rest =>
        apply validate_correct hc hval
        apply ih (input := after) (n := n+1) (step := step+1) (root := next) (prior := c::prior)
        · intro a ha
          rcases List.mem_cons.mp ha with rfl|old
          · exact hc
          · exact hp _ old
        · exact hn
        · simpa only [segment,hd,hval,evaluated_eq] using ok

def previous (published : Nat → Claims) : Nat → List Clause
  | 0 => []
  | k+1 => ((published k).map Prod.snd).reverse ++ previous published k

def expected (steps : Nat) (published : Claims) (isLast : Bool) : Claims :=
  published ++ (if isLast then [(steps-1,[])] else [])

theorem complete {source : Nat → Clause} {v} (hs : ∀ i, holds v (source i))
    (enabled : Nat → Bool) (hinted : Bool) (start : Nat → State) (length : Nat → Nat) (published : Nat → Claims)
    (last : Nat) (checked : ∀ j ≤ last,
      segment source (chooseReason hinted source enabled) packet 500000 (length j) 0 (previous published j).length
          0 (previous published j) (start j) (expected (length j) (published j) (j == last))=true) : False := by
  have initial : respects v 0 := by intro l bit; simp at bit
  have accumulated (j : Nat) (hj : j≤last) : ∀ c ∈ previous published j, holds v c := by
    induction j with
    | zero => intro c hc; cases hc
    | succ k ih =>
      have small : k≤last := by omega
      have h := segment_sound hs (ih small) initial (checked k small)
      intro c member
      rw [previous,List.mem_append] at member
      rcases member with new|old
      · rw [List.mem_reverse,List.mem_map] at new
        obtain ⟨o,ho,rfl⟩ := new
        exact h o (List.mem_append_left _ ho)
      · exact ih small c old
  have h := segment_sound hs (accumulated last (le_refl _)) initial (checked last (le_refl _))
  have inc : (length last-1,[]) ∈ expected (length last) (published last) (last == last) := by simp [expected]
  obtain ⟨_,m,_⟩ := h _ inc
  cases m

end PriorG11.Blocks

namespace PriorG11.Blocks
open PriorG11.Learning PriorG11.Stream PriorG11.Compressed

def parseLits : Nat → Nat → Nat → Clause × Nat
  | 0,_,pos => ([],pos)
  | n+1,base,pos =>
    let (d,after) := claimNumber (if base=0 then 3 else 4) pos
    let v := base+d
    let (xs,next) := parseLits n (v+1) after
    ((v/2,v % 2 == 1)::xs,next)

def parseClaims : Nat → Nat → Nat → Claims
  | 0,_,_ => []
  | n+1,base,pos =>
    let (gap,more) := claimNumber 1 pos
    let (count,after) := claimNumber 2 more
    let (clause,next) := parseLits count 0 after
    let step := base+gap
    (step,clause)::parseClaims n (step+1) next

def firstBlock (i : Nat) := little (casesAt+3*i) 2
def blockCount (i : Nat) := byte (casesAt+3*i+2)
def lengthOf (b : Nat) := little (blocksAt+7*b+3) 2
def startOf (b : Nat) : State :=
  let first := proofsAt+little (blocksAt+7*b) 3
  (makeCursor (little first 4) (first+4),0)
def claimsOf (b : Nat) : Claims :=
  strict (little (blocksAt+7*b+5) 2) fun offset =>
  if offset=0 then [] else
    let (count,after) := claimNumber 0 (8*(claimsAt+offset-1))
    parseClaims count 0 after

def oneBlock (cell j : Nat) (source : Nat → Clause) (enabled : Nat → Bool) : Bool :=
  let first := firstBlock cell
  let last := blockCount cell-1
  let b := first+j
  let prior := previous (fun k => claimsOf (first+k)) j
  segment source (chooseReason (useHints cell) source enabled) packet 500000 (lengthOf b) 0 prior.length 0 prior
    (startOf b) (expected (lengthOf b) (claimsOf b) (j == last))

def whole (cell : Nat) (source : Nat → Clause) (enabled : Nat → Bool) : Bool :=
  let last := blockCount cell-1
  (List.range (last+1)).all fun j => oneBlock cell j source enabled

theorem whole_sound {v source enabled cell} (hs : ∀ i, holds v (source i)) :
    whole cell source enabled = false := by
  cases chk : whole cell source enabled with
  | false => rfl
  | true =>
    exfalso
    apply complete hs enabled (useHints cell) (fun j => startOf (firstBlock cell+j)) (fun j => lengthOf (firstBlock cell+j))
      (fun j => claimsOf (firstBlock cell+j)) (blockCount cell-1)
    intro j hj
    exact List.all_eq_true.mp chk j (List.mem_range.mpr (by omega))

end PriorG11.Blocks

namespace PriorG11.Proof
open SharedCases Bounds Learning Blocks

def active [Slice] (b : CellData) : Nat → Bool :=
  Rup.enS b.budget b.independentMask b.mode b.symmetry b.pins b.pairs b.masks

def reason [Slice] (b : CellData) (key : Nat) : Clause :=
  if active b key then Rup.expS b.budget b.independentMask b.mode b.pins b.pairs b.masks key else tautology

def before (i : Fin 4) : Nat := match i.val with
  | 0 => 0 | 1 => 126 | 2 => 197 | _ => 325

def number (i : Fin 4) (j : Nat) := (blockCount (before i+j)-1)+1

def atBlock (i : Fin 4) (j s : Nat) : Bool :=
  let b := (cellsAt i).getD j default
  oneBlock (before i+j) s (@reason ⟨i⟩ b) (@active ⟨i⟩ b)

abbrev Works (i : Fin 4) (j : Nat) := ∀ s < number i j, atBlock i j s=true
abbrev Successful := ∀ i : Fin 4, ∀ j < (cellsAt i).length, Works i j
abbrev Span (i : Fin 4) (start finish : Nat) := ∀ j, start≤j → j<finish → Works i j

theorem appendSpan {i a b c} (l : Span i a b) (r : Span i b c) : Span i a c := by
  intro j ha hc
  by_cases h : j<b
  · exact l j ha h
  · exact r j (by omega) hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x0 : Span 0 0 39 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x1 : Span 0 39 53 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x2 : Span 0 53 63 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x3 : Span 0 63 85 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x4 : Span 0 85 115 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x5 : Span 0 115 126 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x0 : Span 1 0 20 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x1 : Span 1 20 38 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x2 : Span 1 38 52 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x3 : Span 1 52 57 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x4 : Span 1 57 61 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 4 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x5 : Span 1 61 71 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x0 : Span 2 0 32 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x1 : Span 2 32 50 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 3 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x2 : Span 2 50 63 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x3 : Span 2 63 89 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x4 : Span 2 89 113 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x5 : Span 2 113 128 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x0 : Span 3 0 46 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x1 : Span 3 46 73 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x2 : Span 3 73 80 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x3 : Span 3 80 113 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 3 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x4 : Span 3 113 120 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x5 : Span 3 120 137 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 3 at hs) <;> interval_cases s <;> decide +kernel
theorem successful : Successful := by
  intro i
  fin_cases i
  · intro j hj
    exact (appendSpan range0x0 (appendSpan range0x1 (appendSpan range0x2 (appendSpan range0x3 (appendSpan range0x4 range0x5))))) j (Nat.zero_le j) hj
  · intro j hj
    exact (appendSpan range1x0 (appendSpan range1x1 (appendSpan range1x2 (appendSpan range1x3 (appendSpan range1x4 range1x5))))) j (Nat.zero_le j) hj
  · intro j hj
    exact (appendSpan range2x0 (appendSpan range2x1 (appendSpan range2x2 (appendSpan range2x3 (appendSpan range2x4 range2x5))))) j (Nat.zero_le j) hj
  · intro j hj
    exact (appendSpan range3x0 (appendSpan range3x1 (appendSpan range3x2 (appendSpan range3x3 (appendSpan range3x4 range3x5))))) j (Nat.zero_le j) hj
end PriorG11.Proof
namespace PriorG11.SharedCases
variable [sctx : Slice]
section
private abbrev tS (n:Nat):=Finset (Fin n)
private abbrev tX (n:Nat):=Fin n->Bool
private abbrev tY (n:Nat):=Fin n->Nat
private abbrev tK:=Finset Nat
private abbrev tL:=List Bool
private abbrev tJ:=Nat×Bool
private abbrev tG:=Bool×Nat×Nat
private abbrev tF:=Finset
open List renaming all_eq_true->p0,any_cons->p1,any_eq_true->p2,getD_eq_getElem?_getD->p3,getElem?_append_left->p4,getElem?_eq_getElem->p5,getElem?_map->p6,getElem_of_mem->p7,length_ofFn->p8,length_singleton->p9,length_take->p10,map_append->p11,map_cons->p12,map_nil->p13,mem_cons_self->p14,mem_filter->p15,mem_map->p16,mem_range->p17,mem_toFinset->p18,nodup_append->p19,range->p20,toFinset_card_of_nodup->p21
open Nat renaming find->p22,find_min->p23,find_spec->p24,not_lt->p25,one_shiftLeft->p26,testBit_or->p27,zero_testBit->p28
open Finset renaming card_eq_one->p29,card_filter->p30,card_filter_add_card_filter_not->p31,card_image_of_injOn->p32,card_image_of_injective->p33,card_le_card->p34,card_sdiff_add_card_eq_card->p35,disjoint_left->p36,eq_empty_of_forall_notMem->p37,filter_filter->p38,image_nonempty->p39,inter_subset_right->p40,le_max'->p41,max'_mem->p42,mem_insert->p43,mem_sigma->p44,mem_toList->p45,one_lt_card->p46,range->p47,singleton_injective->p48,singleton_subset_iff->p49,sum_add_distrib->p50,sum_congr->p51,sum_eq_zero->p52,univ->p53
open Bool renaming eq_false_iff->p54,false->p55,false_and->p56,false_or->p57,noConfusion->p58,not_eq_false->p59,not_not->p60,not_true->p61,or_assoc->p62,true->p63,true_and->p64
open Prod renaming fst->p65
open Sum (inl inr)
open List renaming length->tD
namespace DagTools
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset (mem_coe mem_biUnion sum_subset mem_product filter_congr univ)
namespace A0
abbrev RT:=@Relation.ReflTransGen
abbrev rC:=@Relation.ReflTransGen.cases_head
abbrev rI:=@Relation.ReflTransGen.head_induction_on
abbrev sI:=@Nat.strong_induction_on
abbrev oF:=@List.ofFn
lemma lL{a b c:Nat}:a<b->b<=c->a<c:=lt_of_lt_of_le
lemma dT{p:Prop}[Decidable p]:(decide p=p63)=p:=decide_eq_true_eq
lemma m0{α}[DecidableEq α](a:α):a∈({a}:tF α):=Finset.mem_singleton_self a
noncomputable abbrev cP:=@Classical.decPred
lemma bA{a b:Bool}:((a&&b)=p63)=(a=p63/\b=p63):=Bool.and_eq_true a b
lemma bO{a b:Bool}:((a||b)=p63)=(a=p63\/b=p63):=Bool.or_eq_true a b
abbrev EP:=@Equiv.Perm
lemma mF{α}{s:tF α}{p}[DecidablePred p]{a}:a∈s.filter p<->a∈s/\p a:=Finset.mem_filter
lemma mS{α}[DecidableEq α]{a b:α}:a∈({b}:tF α)<->a=b:=Finset.mem_singleton
lemma mR{n m:Nat}:n∈p47 m<->n<m:=Finset.mem_range
lemma mI{α}[DecidableEq α]{s t:tF α}{a}:a∈s∩t<->a∈s/\a∈t:=Finset.mem_inter
lemma mU{α}[Fintype α](a:α):a∈(p53:tF α):=Finset.mem_univ a
lemma mD{α}[DecidableEq α]{s t:tF α}{a}:a∈s\t<->a∈s/\a∉t:=Finset.mem_sdiff
lemma mG{α β}[DecidableEq β]{f:α->β}{s:tF α}{b}:b∈s.image f<->∃a∈s,f a=b:=Finset.mem_image
lemma mN{α}[DecidableEq α]{s t:tF α}{a}:a∈s∪t<->a∈s\/a∈t:=Finset.mem_union
lemma nE{α}(a:α):a∉(∅:tF α):=Finset.notMem_empty a
abbrev U0:=Σ _:Nat,Nat
abbrev rH:=@Relation.ReflTransGen.head
abbrev rR:=@Relation.ReflTransGen.refl
abbrev rK:=@Relation.ReflTransGen.cases_tail
abbrev rT:=@Relation.ReflTransGen.tail
abbrev fE:=@Finset.eq_empty_iff_forall_notMem
abbrev fS:=@Finset.sum_filter_add_sum_filter_not
abbrev fN:=@Finset.not_nonempty_iff_eq_empty
abbrev fU:=@Finset.card_union_of_disjoint
abbrev fI:=@Finset.inter_subset_left
abbrev lP:=@List.length_pos_of_ne_nil
abbrev lR:=List.finRange
abbrev lS:=@List.mem_singleton
abbrev nA:=@Nat.add_sub_cancel_left
abbrev nL:=@Nat.le_add_right
abbrev bF:=Bool.false_eq_true
abbrev lA:=@List.length_append
abbrev lO:=@List.foldl_cons
abbrev o1:=@Or.inl
abbrev o2:=@Or.inr
abbrev nZ:=@Nat.zero_le
abbrev nO:=@Nat.zero_lt_one
abbrev nT:=@Nat.lt_of_lt_of_le
lemma fw{α}(a:α):({a}:tF α).card=1:=Finset.card_singleton a
abbrev fz:=@Finset.card_pos
abbrev gk:=@Finset.not_nonempty_empty
abbrev g5:=p47
abbrev g6:=@List.mem_append
abbrev g8:=@Finset.card_eq_zero
abbrev gI:=@Finset.filter_eq_empty_iff
abbrev hC:=@List.mem_finRange
abbrev hE:=@Finset.single_le_sum
abbrev hD:=@dite_eq_left
abbrev hF:=@Sum.inl.injEq
abbrev hG:=@List.getElem_append_left
abbrev hH:=@List.getElem_append_right
abbrev hI:=@Option.some.injEq
abbrev hJ:=@Nat.not_lt_zero
abbrev hK:=@List.length_replicate
abbrev hL:=@List.getElem_mem
abbrev hN:=@Finset.card_le_card_of_injOn
abbrev hO:=@Finset.card_filter_le
end A0
section
open A0
def xp:Bool->Bool->Bool->Bool
 | true,a,b=>a&&b
 | false,a,b=>a||b
@[simp] lemma gop_true(a b:Bool):xp p63 a b=(a&&b):=rfl
@[simp] lemma gop_false(a b:Bool):xp p55 a b=(a||b):=rfl
abbrev qD:=List (tG)
abbrev Dag:=qD
def gZ(D:qD)(j:Nat):Bool:=(D.getD j (p55,0,0)).1
def yx(D:qD)(j:Nat):Nat:=(D.getD j (p55,0,0)).2.1
def yf(D:qD)(j:Nat):Nat:=(D.getD j (p55,0,0)).2.2
def zp(w:tL)(g:tG):tL:=w++[xp g.1 (w.getD g.2.1 p55) (w.getD g.2.2 p55)]
def wl(D:qD)(w:tL):tL:=D.foldl zp w
def fO(D:qD){n:Nat}(x:tX n)(w:Nat):Bool:=(wl D (oF x)).getD w p55
abbrev val(D:qD){n:Nat}:=@fO D n
def q0(n:Nat)(D:qD):Prop:=∀j,j<(tD D)->yx D j<n+j/\yf D j<n+j/\yx D j≠yf D j
def qg(D:qD)(w:Nat):tK:=(g5 (tD D)).filter (λ j=>yx D j=w\/yf D j=w)
def fanout (D:qD)(w:Nat):Nat:=(qg D w).card
def b5(n:Nat)(D:qD):Prop:=∀w,w+1<n+(tD D)->1<=fanout D w
def fV(n:Nat)(D:qD):Prop:=q0 n D/\b5 n D/\D≠[]
abbrev StrictLive:=fV
def qb(n:Nat)(D:qD):Nat:=n+(tD D)-1
def q9{n:Nat}(v:Fin n):tX n:=λ i=>decide (i=v)
def fM(n:Nat)(D:qD)(w:Nat):tS n:=univ.filter (λ v=>fO D (q9 v) w=p63)
abbrev supp:=fM
def q6(D:qD)(K:tK):Nat:=∑ w∈K,(fanout D w-1)
def inner(n:Nat)(D:qD):tK:=g5 (n+(tD D)-1)
def yr(n:Nat)(D:qD):Nat:=q6 D (inner n D)
def fJ(n:Nat)(D:qD):Nat:=q6 D ((inner n D).filter (λ w=>(fM n D w).Nonempty))
def Bzero (n:Nat)(D:qD):Nat:=q6 D ((inner n D).filter (λ w=>¬(fM n D w).Nonempty))
def kl(n:Nat)(D:qD):tK:=(g5 (n+(tD D))).filter (λ w=>2<=fanout D w)
def fX(n:Nat)(D:qD):tS n:=(kl n D).biUnion (fM n D)
def ineligSet (n:Nat)(D:qD):Finset (Fin n):=univ \ fX n D
def units(n:Nat)(D:qD):tF U0:=(inner n D).sigma (λ w=>g5 (fanout D w-1))
def ww(n:Nat)(D:qD):tF U0:=(units n D).filter (λ u=>(fM n D u.1).Nonempty)
def jw(D:qD):tF (tJ):=g5 (tD D)×ˢ p53
def fC(D:qD)(e:tJ):Nat:=if e.2=p63 then yf D e.1 else yx D e.1
def qc(n:Nat)(D:qD)(K:tK):tF (tJ):=(jw D).filter (λ e=>fC D e∈K/\n+e.1∉K)
def w5(n:Nat)(D:qD)(K:tK):tK:=(g5 (tD D)).filter (λ j=>n+j∈K/\yx D j∈K/\yf D j∈K)
def z8(n:Nat)(K:tK):tK:=K.filter (λ w=>w<n)
def q2(n:Nat)(D:qD)(T:tS n):tK:=(g5 (n+(tD D))).filter (λ w=>(fM n D w∩T).Nonempty)
def q4(n:Nat)(D:qD)(x y:Fin n):tK:=(g5 (n+(tD D))).filter (λ w=>x∈fM n D w/\y∉fM n D w)
def gN(n:Nat)(D:qD)(b:tY n):Prop:=∀v∈fX n D,2<=fanout D (b v)/\fM n D (b v)={v}
abbrev PureBranch:=gN
def qh(n:Nat)(D:qD)(b:tY n):tF U0:=(fX n D).image (λ v=>(⟨b v,0⟩:U0))
def residualUnits (n:Nat)(D:qD)(b:Fin n->Nat):Finset (U0):=ww n D \ qh n D b
section
variable (D:qD)(j:Nat)(h:j<(tD D))
include D j h
lemma xd :gZ D j=(D[j]).1:=by simp[gZ,p5 h]
lemma xe :yx D j=(D[j]).2.1:=by simp[yx,p5 h]
lemma xf :yf D j=(D[j]).2.2:=by simp[yf,p5 h]
end
lemma km(g:tG)(D:qD)(w:tL):wl (g::D) w=wl D (zp w g):=rfl
lemma vi(D E:qD)(w:tL):wl (D++E) w=wl E (wl D w):=by simp[wl,List.foldl_append]
lemma zf(w:tL)(g:tG):(zp w g).length=w.length+1:=by simp[zp]
lemma jk(D:qD):∀w:tL,(wl D w).length=w.length+(tD D):=by induction D with|nil=>{intro w;simp[wl]}|cons g D ih=>{intro w;rw[km,ih,zf];simp;omega}
lemma jo(w:tL)(g:tG)(i:Nat)(h:i<w.length):(zp w g).getD i p55=w.getD i p55:=by simp[zp,p4 h]
lemma jx(D:qD):∀(w:tL) (i:Nat),i<w.length->(wl D w).getD i p55=w.getD i p55:=by induction D with|nil=>{intro w i _;rfl}|cons g D ih=>{intro w i h;rw[km,ih _ _ (by rw[zf];omega),jo _ _ _ h]}
lemma b6(w:tL)(i:Nat)(h:w.length<=i):w.getD i p55=p55:=by simp[List.getElem?_eq_none h]
lemma zq(w:tL)(g:tG):(zp w g).getD w.length p55=xp g.1 (w.getD g.2.1 p55) (w.getD g.2.2 p55):=by simp[zp]
lemma kn(D:qD)(w:tL)(j:Nat)(a:j<(tD D)):(wl D w).getD (w.length+j) p55=xp (gZ D j) ((wl (D.take j) w).getD (yx D j) p55) ((wl (D.take j) w).getD (yf D j) p55):=by have c:D=D.take j++D[j]::D.drop (j+1):=by{simp};have d:(wl (D.take j) w).length=w.length+j:=by{rw[jk,p10];omega};rw[xd D j a,xe D j a,xf D j a];conv_lhs=>{rw[c,vi,km]};rw[jx _ _ _ (by rw[zf,d];omega),<-d,zq]
lemma zg(D:qD)(w:tL)(j i:Nat)(a:i<w.length+j)(c:j<=(tD D)):(wl (D.take j) w).getD i p55=(wl D w).getD i p55:=by have d:D=D.take j++D.drop j:=by{simp};have g:(wl (D.take j) w).length=w.length+j:=by{rw[jk,p10];omega};conv_rhs=>{rw[d,vi]};rw[jx (D.drop j) (wl (D.take j) w) i (by rw[g];exact a)]
section
variable (D:qD){n:Nat}(x:tX n)
include D n x
lemma qa(i:Nat)(h:i<n):fO D x i=x ⟨i,h⟩:=by unfold fO;rw[jx _ _ _ (by simpa using h)];simp[h]
lemma z0(w:Nat)(h:n+(tD D)<=w):fO D x w=p55:=by unfold fO;exact b6 _ _ (by rw[jk];simpa using h)
lemma xx(k w:Nat)(a:w<n+k)(c:k<=(tD D)):fO (D.take k) x w=fO D x w:=by unfold fO;exact zg D _ k w (by simpa using a) c
end
lemma qu{n:Nat}{D:qD}(c:q0 n D)(x:tX n)(j:Nat)(a:j<(tD D)):fO D x (n+j)=xp (gZ D j) (fO D x (yx D j)) (fO D x (yf D j)):=by obtain⟨g,d,-⟩:=c j a;have h:=kn D (oF x) j a;simp only[p8] at h;unfold fO;rw[h,zg D _ j _ (by simpa using g) a.le,zg D _ j _ (by simpa using d) a.le]
lemma jy{n:Nat}{D:qD}(c:q0 n D)(x:tX n)(f:Nat->Bool)(a:∀i (h:i<n),f i=x ⟨i,h⟩)(d:∀j,j<(tD D)->f (n+j)=xp (gZ D j) (f (yx D j)) (f (yf D j))):∀w,w<n+(tD D)->fO D x w=f w:=by intro w;induction w using sI with|_ w ih=>{intro q;by_cases l:w<n;{rw[qa D x w l,a w l]};{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have g:j<(tD D):=by{omega};obtain⟨p,m,-⟩:=c j g;rw[qu c x j g,d j g,ih _ p (by omega),ih _ m (by omega)]}}
abbrev ko:=Bool ⊕ Nat
def qv(W:tL):ko->Bool
 | inl b=>b
 | inr k=>W.getD k p55
def wz(m:List ko)(i:Nat):ko:=m.getD i (inl p55)
def wf(t:Bool):ko->ko->ko ⊕ (Nat×Nat)
 | inl a,r=>inl (if a=t then r else inl a)
 | inr i,inl b=>inl (if b=t then inr i else inl b)
 | inr i,inr j=>if i=j then inl (inr i) else inr (i,j)
def w9:GateOp->Bool
 | GateOp.and=>p63
 | _=>p55
def qi(n:Nat)(st:List ko×qD)(g:Gate):List ko×qD:=match g.inputs with|[]=>(st.1++[inl (w9 g.op)],st.2)|[a]=>(st.1++[wz st.1 a],st.2)|a::b::_=>match wf (w9 g.op) (wz st.1 a) (wz st.1 b) with|inl r=>(st.1++[r],st.2)|inr p=>(st.1++[inr (n+st.2.length)],st.2++[(w9 g.op,p.1,p.2)])
def jp(B:Nat):ko->Prop
 | inl _=>True
 | inr k=>k<B
def v6(n:Nat)(st:List ko×qD):Prop:=q0 n st.2/\∀r∈st.1,jp (n+st.2.length) r
lemma xg{B a:Nat}(h:B<=a)(r:ko)(c:jp B r):jp a r:=by rcases r with b|k;{trivial};{exact lL c h}
lemma yg(W:tL)(m:List ko)(i:Nat):qv W (wz m i)=(m.map (qv W)).getD i p55:=by simp only[wz,p3,p6];cases m[i]?<;>rfl
lemma zh(B:Nat)(m:List ko)(a:∀r∈m,jp B r)(i:Nat):jp B (wz m i):=by simp only[wz,p3];rcases h:m[i]? with _|r;{trivial};{exact a r (List.mem_of_getElem? h)}
lemma vs(W:tL)(g:tG)(r:ko)(a:jp W.length r):qv (zp W g) r=qv W r:=by rcases r with b|k;{rfl};{exact jo W g k a}
lemma x5(t:Bool)(W:tL)(a b r:ko)(h:wf t a b=inl r):qv W r=xp t (qv W a) (qv W b):=by rcases a with a|i;{simp only[wf,hF] at h;subst h;cases t<;>cases a<;>simp[qv]};{rcases b with b|j;{simp only[wf,hF] at h;subst h;cases t<;>cases b<;>simp[qv]};{simp only[wf] at h;split_ifs at h with hij;simp only[hF] at h;subst h;subst hij;cases t<;>simp[qv]}}
lemma xh(B:Nat)(t:Bool)(a b r:ko)(c:jp B a)(d:jp B b)(h:wf t a b=inl r):jp B r:=by rcases a with a|i;{simp only[wf,hF] at h;subst h;split_ifs;{exact d};{trivial}};{rcases b with b|j;{simp only[wf,hF] at h;subst h;split_ifs;{exact c};{trivial}};{simp only[wf] at h;split_ifs at h;simp only[hF] at h;subst h;exact c}}
lemma x6(t:Bool)(a b:ko)(p:Nat×Nat)(h:wf t a b=inr p):a=inr p.1/\b=inr p.2/\p.1≠p.2:=by rcases a with a|i;{simp[wf] at h};{rcases b with b|j;{simp[wf] at h};{simp only[wf] at h;split_ifs at h with hij;cases h;exact⟨rfl,rfl,hij⟩}}
section
variable (op:GateOp)(a:op∈({GateOp.and,GateOp.or}:Set GateOp))
include op a
lemma xz :op.eval []=w9 op:=by rcases a with rfl|rfl<;>rfl
lemma b3(u:Bool):op.eval [u]=u:=by rcases a with rfl|rfl<;>simp[GateOp.eval]
lemma x7(u v:Bool):op.eval [u,v]=xp (w9 op) u v:=by rcases a with rfl|rfl<;>simp[GateOp.eval,w9]
end
lemma v7(D E:qD)(k:Nat)(h:k<(tD D)):(D++E).getD k (p55,0,0)=D.getD k (p55,0,0):=by simp[p4 h]
lemma kp(D:qD)(g:tG):(D++[g]).getD (tD D) (p55,0,0)=g:=by simp[]
lemma vz{n:Nat}{D:qD}(d:q0 n D)(t:Bool)(i j:Nat)(c:i<n+(tD D))(a:j<n+(tD D))(l:i≠j):q0 n (D++[(t,i,j)]):=by intro k m;simp only[lA,p9] at m;by_cases h:k<(tD D);{simp only[yx,yf,v7 D _ k h];exact d k h};{have g:k=(tD D):=by{omega};subst g;simp only[yx,yf,kp];exact⟨c,a,l⟩}
lemma k1{n:Nat}{D:qD}(a:q0 n D)(k:Nat):q0 n (D.take k):=by intro j g;simp only[p10] at g;have d:j<k:=by{omega};have c:j<(tD D):=by{omega};have e:(D.take k).getD j (p55,0,0)=D.getD j (p55,0,0):=by{simp[d]};simp only[yx,yf,e];exact a j c
lemma kq(n:Nat)(st:List ko×qD)(g:Gate)(d:g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2)(h:v6 n st):v6 n (qi n st g)/\(qi n st g).2.length<=st.2.length+1/\∀(x:tX n) (w:tL),st.1.map (qv (wl st.2 (oF x)))=w->(qi n st g).1.map (qv (wl (qi n st g).2 (oF x)))=w++[g.op.eval (g.inputs.map λ i=>w.getD i p55)]:=by obtain⟨m,D⟩:=st;obtain⟨op,L⟩:=g;obtain⟨q,v⟩:=d;obtain⟨J,l⟩:=h;dsimp only at J l q v ⊢;rcases L with _|⟨a,_|⟨b,_|⟨c,P⟩⟩⟩;{exact⟨⟨J,λ r j=>by{simp only[qi,g6,lS] at j;rcases j with j|rfl;exact l r j;trivial}⟩,by simp[qi],λ x w y=>by{subst y;simp only[qi,p11,p12,p13,qv,xz op q]}⟩};{exact⟨⟨J,λ r j=>by{simp only[qi,g6,lS] at j;rcases j with j|rfl;exact l r j;exact zh _ m l a}⟩,by simp[qi],λ x w y=>by{subst y;simp only[qi,p11,p12,p13,b3 op q,yg]}⟩};{have H:=zh _ m l a;have z:=zh _ m l b;rcases hc:wf (w9 op) (wz m a) (wz m b) with r|p;{exact⟨⟨by simpa only[qi,hc] using J,λ K j=>by{simp only[qi,hc,g6,lS] at j ⊢;rcases j with j|rfl;exact l K j;exact xh _ _ _ _ _ H z hc}⟩,by simp[qi,hc],λ x w y=>by{subst y;simp only[qi,hc,p11,p12,p13,x7 op q,x5 _ (wl D (oF x)) _ _ _ hc,yg]}⟩};{obtain⟨R,Q,M⟩:=x6 _ _ _ _ hc;rw[R] at H;rw[Q] at z;exact⟨⟨by simpa only[qi,hc] using vz J (w9 op) p.1 p.2 H z M,λ K j=>by{simp only[qi,hc,g6,lS,lA,p9] at j ⊢;rcases j with j|rfl;exact xg (by omega) K (l K j);show n+(tD D)<n+((tD D)+1);omega}⟩,by simp[qi,hc],λ x w y=>by{subst y;have u:=jk D (oF x);rw[p8] at u;have hW':wl (D++[(w9 op,p.1,p.2)]) (oF x)=zp (wl D (oF x)) (w9 op,p.1,p.2):=by{rw[vi];rfl};have X:m.map (qv (zp (wl D (oF x)) (w9 op,p.1,p.2)))=m.map (qv (wl D (oF x))):=List.map_congr_left (λ r j=>vs _ _ r (u.symm▸l r j));have U:(zp (wl D (oF x)) (w9 op,p.1,p.2)).getD (n+(tD D)) p55=xp (w9 op) ((m.map (qv (wl D (oF x)))).getD a p55) ((m.map (qv (wl D (oF x)))).getD b p55):=by{rw[<-u,zq,<-yg,<-yg,R,Q];rfl};simp only[qi,hc,hW',p11,p12,p13,X,qv,U,x7 op q]}⟩}};{simp at v}
lemma kr(n:Nat)(a:List Gate)(c:∀g∈a,g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2):∀st:List ko×qD,v6 n st->v6 n (a.foldl (qi n) st)/\(a.foldl (qi n) st).2.length<=st.2.length+a.length/\∀(x:tX n) (w:tL),st.1.map (qv (wl st.2 (oF x)))=w->(a.foldl (qi n) st).1.map (qv (wl (a.foldl (qi n) st).2 (oF x)))=a.foldl (λ w g=>w++[g.op.eval (g.inputs.map λ i=>w.getD i p55)]) w:=by induction a with|nil=>{exact λ st h=>⟨h,by simp,λ _ _ d=>d⟩}|cons g a ih=>{intro st h;obtain⟨q,v,p⟩:=kq n st g (c g (by simp)) h;obtain⟨m,u,l⟩:=ih (λ r j=>c r (by simp[j])) _ q;exact⟨m,by{simp only[lO,List.length_cons];omega},λ x w d=>by{simp only[lO];exact l x _ (p x w d)}⟩}
lemma b7(n:Nat)(x:tX n):((p20 n).map inr).map (qv (wl ([]:qD) (oF x)))=oF x:=by apply List.ext_getElem;{simp};{intro i a c;simp only[List.length_map,List.length_range] at a;simp[qv,wl,a]}
lemma z3{n:Nat}(C:Circuit)(a:Monotone2 C):(∃b:Bool,∀x:tX n,C.eval (oF x)=b)\/(∃i:Fin n,∀x:tX n,C.eval (oF x)=x i)\/(∃D:qD,q0 n D/\D≠[]/\(tD D)<=C.size/\∀x:tX n,fO D x (qb n D)=C.eval (oF x)):=by obtain⟨⟨v,l⟩,d,c⟩:=kr n C.gates a ((p20 n).map inr,([]:qD)) ⟨λ j z=>absurd z (by simp),λ r g=>by{simp only[p16,p17] at g;obtain⟨k,hk,rfl⟩:=g;simpa[jp] using hk}⟩;generalize C.gates.foldl (qi n) ((p20 n).map inr,([]:qD))=st at v l d c;obtain⟨m,D⟩:=st;dsimp only at v l d c;have p:∀x:tX n,C.eval (oF x)=qv (wl D (oF x)) (wz m C.output):=λ x=>by{rw[yg,c x (oF x) (b7 n x)];rfl};have hk:=zh _ m l C.output;rcases g:wz m C.output with b|k;{exact .inl ⟨b,λ x=>by{rw[p x,g];rfl}⟩};{rw[g] at hk;have hk':k<n+(tD D):=hk;by_cases q:k<n;{exact .inr (.inl ⟨⟨k,q⟩,λ x=>by{rw[p x,g];exact qa D x k q}⟩)};{have u:(D.take (k-n+1)).length=k-n+1:=by{rw[p10];omega};exact .inr (.inr ⟨D.take (k-n+1),k1 v _,λ h=>by{rw[h] at u;simp at u},by{simp only[List.length_nil,Nat.zero_add] at d;unfold Circuit.size;omega},λ x=>by{have y:qb n (D.take (k-n+1))=k:=by{unfold qb;rw[u];omega};rw[y,xx D x (k-n+1) k (by omega) (by omega),p x,g];rfl}⟩)}}
lemma zi{D:qD}{w:Nat}(h:fanout D w=0)(j:Nat)(a:j<(tD D)):yx D j≠w/\yf D j≠w:=by unfold fanout qg at h;rw[g8,gI] at h;have:=h (mR.2 a);tauto
def v8(c a:Nat):Nat:=if c<a then a-1 else a
def qw(c w:Nat):Nat:=if w<c then w else w+1
def y0(n j:Nat)(D:qD):qD:=(D.eraseIdx j).map (λ g=>(g.1,v8 (n+j) g.2.1,v8 (n+j) g.2.2))
lemma yb(n j:Nat)(D:qD)(a:j<(tD D)):(y0 n j D).length=(tD D)-1:=by simp[y0,List.length_eraseIdx,a]
lemma k2(n j:Nat)(D:qD)(k:Nat)(c:qw j k<(tD D)):gZ (y0 n j D) k=gZ D (qw j k)/\yx (y0 n j D) k=v8 (n+j) (yx D (qw j k))/\yf (y0 n j D) k=v8 (n+j) (yf D (qw j k)):=by have e:(y0 n j D).getD k (p55,0,0)=((D.getD (qw j k) (p55,0,0)).1,v8 (n+j) (D.getD (qw j k) (p55,0,0)).2.1,v8 (n+j) (D.getD (qw j k) (p55,0,0)).2.2):=by{simp only[y0,p3,p6,List.getElem?_eraseIdx];unfold qw at c ⊢;split_ifs at c ⊢<;>simp[p5 c]};unfold gZ yx yf;rw[e];exact⟨rfl,rfl,rfl⟩
section
variable {n:Nat}{D:qD}(g:q0 n D)(j:Nat)(c:j<(tD D))(d:fanout D (n+j)=0)
include n D g j c d
lemma jq :q0 n (y0 n j D):=by intro k u;rw[yb n j D c] at u;have hk':qw j k<(tD D):=by{unfold qw;split_ifs<;>omega};have h:(k<j/\qw j k=k)\/(j<=k/\qw j k=k+1):=by{unfold qw;split_ifs<;>omega};obtain⟨r,q,i⟩:=g _ hk';obtain⟨ra,p⟩:=zi d _ hk';obtain⟨-,m,l⟩:=k2 n j D k hk';rw[m,l];generalize qw j k=k' at *;generalize yx D k'=a at *;generalize yf D k'=b at *;refine⟨?_,?_,?_⟩<;>unfold v8<;>split_ifs<;>omega
lemma xi(x:tX n)(w:Nat)(h:w<n+((tD D)-1)):fO (y0 n j D) x w=fO D x (qw (n+j) w):=by refine jy (jq g j c d) x (λ u=>fO D x (qw (n+j) u)) (λ i l=>by{show fO D x (qw (n+j) i)=_;rw[show qw (n+j) i=i by{unfold qw;split_ifs<;>omega}];exact qa D x i l}) (λ k y=>by{rw[yb n j D c] at y;have hk':qw j k<(tD D):=by{unfold qw;split_ifs<;>omega};obtain⟨q,v,r⟩:=k2 n j D k hk';obtain⟨ra,p⟩:=zi d _ hk';have m:∀a,a≠n+j->qw (n+j) (v8 (n+j) a)=a:=λ a z=>by{unfold qw v8;split_ifs<;>omega};show fO D x (qw (n+j) (n+k))=_;rw[show qw (n+j) (n+k)=n+qw j k by{unfold qw;split_ifs<;>omega},q,v,r,m _ ra,m _ p];exact qu g x _ hk'}) w (by{rw[yb n j D c];exact h})
end
section
variable {n:Nat}(F:(tX n)->Bool)(a:∀i:Fin n,∃x y:tX n,(∀k,k≠i->x k=y k)/\F x≠F y)
include n F a
lemma x8 :∀(s:Nat) (D:qD),(tD D)=s->q0 n D->D≠[]->(∀x:tX n,fO D x (qb n D)=F x)->∃D':qD,fV n D'/\D'.length<=s/\∀x:tX n,fO D' x (qb n D')=F x:=by intro s;induction s using sI with|_ s ih=>{intro D r z q K;have Q:0<(tD D):=lP q;by_cases U:b5 n D;{exact⟨D,⟨z,U,q⟩,r.le,K⟩};{obtain⟨w,P,d⟩:∃w,w+1<n+(tD D)/\fanout D w=0:=by_contra λ v=>U (λ w P=>by_contra λ h0=>v ⟨w,P,by omega⟩);by_cases m:w<n;{obtain⟨x,y,L,H⟩:=a ⟨w,m⟩;exact absurd (by{rw[<-K x,<-K y];have p:qb n D≠w:=by{unfold qb;omega};have l:=jy z y (λ u=>if u=w then y ⟨w,m⟩ else fO D x u) (λ i R=>by{by_cases c:i=w;subst c;simp;simp only[c,ite_false];rw[qa D x i R];exact L ⟨i,R⟩ (λ h=>c (congrArg Fin.val h))}) (λ j g=>by{obtain⟨ha,Z⟩:=zi d j g;have M:n+j≠w:=by{omega};simp only[M,ha,Z,ite_false];exact qu z x j g}) (qb n D) (by{unfold qb;omega});simp only[p,ite_false] at l;exact l.symm}) H};{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have g:j<(tD D):=by{omega};have J:=yb n j D g;obtain⟨D',h1,h2,h3⟩:=ih ((tD D)-1) (by omega) (y0 n j D) J (jq z j g d) (λ h=>by{rw[h] at J;simp at J;omega}) (λ x=>by{have Y:qb n (y0 n j D)=n+((tD D)-1)-1:=by{unfold qb;rw[J]};have X:qw (n+j) (n+((tD D)-1)-1)=qb n D:=by{unfold qw qb;split_ifs<;>omega};rw[Y,xi z j g d x _ (by omega),X];exact K x});exact⟨D',h1,by omega,h3⟩}}}
lemma yt(D:qD)(d:q0 n D)(c:D≠[])(g:∀x:tX n,fO D x (qb n D)=F x):∃D':qD,fV n D'/\D'.length<=(tD D)/\∀x:tX n,fO D' x (qb n D')=F x:=x8 F a (tD D) D rfl d c g
end
lemma zy{n:Nat}(C:Circuit)(a:Monotone2 C)(g:∀b:Bool,∃x:tX n,C.eval (oF x)≠b)(d:∀i:Fin n,∃x:tX n,C.eval (oF x)≠x i)(c:∀i:Fin n,∃x y:tX n,(∀k,k≠i->x k=y k)/\C.eval (oF x)≠C.eval (oF y)):∃D:qD,fV n D/\(tD D)<=C.size/\∀x:tX n,fO D x (qb n D)=C.eval (oF x):=by rcases z3 (n:=n) C a with ⟨b,p⟩|⟨i,m⟩|⟨D,q,j,l,r⟩;{obtain⟨x,h⟩:=g b;exact absurd (p x) h};{obtain⟨x,h⟩:=d i;exact absurd (m x) h};{obtain⟨D',v,z,u⟩:=yt (λ x=>C.eval (oF x)) c D q j r;exact⟨D',v,by omega,u⟩}
section
variable {n:ℕ} {D:qD}
lemma ql{w:Nat}:w∈inner n D↔w+1<n+(tD D):=by unfold inner;rw[mR];omega
lemma qf(j:Nat):fC D (j,p55)=yx D j:=by simp[fC]
lemma qo(j:Nat):fC D (j,p63)=yf D j:=by simp[fC]
lemma qz(a:q0 n D)(w:Nat)(h:n+(tD D)<=w+1):fanout D w=0:=by unfold fanout qg;rw[g8,gI];intro j d;have c:=mR.1 d;have:=a j c;omega
lemma wk(a:q0 n D){w:Nat}(h:1<=fanout D w):w+1<n+(tD D):=by by_contra c;have:=qz a w (by omega);omega
lemma yo(P:tJ->Prop) [DecidablePred P]:((jw D).filter P).card=∑ j∈g5 (tD D),((if P (j,p55) then 1 else 0)+(if P (j,p63) then 1 else 0)):=by rw[p30,jw,Finset.sum_product];refine p51 rfl (λ j _=>?_);rw[Fintype.sum_bool,add_comm]
lemma ks:(jw D).card=2*(tD D):=by simp[jw,Finset.card_product,Nat.mul_comm]
lemma xq(d:q0 n D)(e:tJ)(a:e∈jw D):fC D e+1<n+(tD D):=by obtain⟨j,c⟩:=e;have g:j<(tD D):=by{simpa[jw] using a};have:=d j g;cases c;{rw[qf];omega};{rw[qo];omega}
lemma k3(a:q0 n D)(w:Nat):fanout D w=((jw D).filter (λ e=>fC D e=w)).card:=by rw[yo,fanout,qg,p30];refine p51 rfl (λ j c=>?_);have:=(a j (mR.1 c)).2.2;rw[qf,qo];split_ifs<;>omega
lemma zd(a:q0 n D)(K:tK):∑ w∈K,fanout D w=((jw D).filter (λ e=>fC D e∈K)).card:=by rw[Finset.card_eq_sum_card_fiberwise (f:=fC D) (s:=(jw D).filter (λ e=>fC D e∈K)) (t:=K) (λ e c=>mem_coe.2 (mF.1 (mem_coe.1 c)).2)];refine p51 rfl (λ w d=>by{rw[k3 a,p38];congr 1;ext e;simp only[mF];exact⟨λ⟨c,rfl⟩=>⟨c,d,rfl⟩,λ⟨c,_,h⟩=>⟨c,h⟩⟩})
lemma yp{K:tK}(a:∀w∈K,1<=fanout D w):q6 D K+K.card=∑ w∈K,fanout D w:=by rw[q6,Finset.card_eq_sum_ones,<-p50];exact p51 rfl (λ w c=>Nat.sub_add_cancel (a w c))
lemma vj(h:fV n D):yr n D+n=(tD D)+1:=by obtain⟨d,j,a⟩:=h;have:=lP a;have:=yp (λ w g=>j w (ql.1 g));have:∑ w∈inner n D,fanout D w=2*(tD D):=by{rw[zd d,Finset.filter_true_of_mem (λ e i=>ql.2 (xq d e i)),ks]};have:(inner n D).card=n+(tD D)-1:=Finset.card_range _;unfold yr;omega
lemma jz(n:Nat)(D:qD):yr n D=fJ n D+Bzero n D:=by unfold yr fJ Bzero q6;exact (fS _ _ _).symm
lemma vk(h:fV n D)(w:Nat)(c:w<n+(tD D)):RT (λ a b=>b<n+(tD D)/\n<=b/\(yx D (b-n)=a\/yf D (b-n)=a)) w (qb n D):=by obtain⟨l,m,-⟩:=h;generalize hk:n+(tD D)-w=k;induction k using sI generalizing w with|_ k ih=>{by_cases g:w+1=n+(tD D);{rw[show w=qb n D by{unfold qb;omega}]};{obtain⟨j,i⟩:=fz.1 (m w (by omega));simp only[qg,mF,mR] at i;have:=l j i.1;exact rH (b:=n+j) ⟨by omega,by omega,by simpa using i.2⟩ (ih (n+(tD D)-(n+j)) (by omega) (n+j) (by omega) rfl)}}
lemma w3{v:Fin n}{w:Nat}:v∈fM n D w↔fO D (q9 v) w=p63:=by simp[fM]
lemma x9(c:q0 n D)(x y:tX n)(a:∀i,x i=p63->y i=p63)(w:Nat):fO D x w=p63->fO D y w=p63:=by induction w using sI with|_ w ih=>{by_cases g:w<n;{rw[qa D x w g,qa D y w g];exact a _};{by_cases m:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have d:j<(tD D):=by{omega};obtain⟨l,h,-⟩:=c j d;rw[qu c x j d,qu c y j d];have:=ih _ l;have:=ih _ h;cases gZ D j<;>simp only[gop_true,gop_false,bA,bO]<;>tauto};{rw[z0 D x w (by omega)];simp}}}
lemma wc(D:qD)(i:Fin n):fM n D i.1={i}:=by ext v;rw[w3,qa D (q9 v) i.1 i.2];simp[q9,eq_comm]
lemma xn(D:qD)(w:Nat)(h:n+(tD D)<=w):fM n D w=∅:=by ext v;simp[w3,z0 D (q9 v) w h]
lemma yy(c:q0 n D)(j:Nat)(a:j<(tD D)):fM n D (n+j)=if gZ D j=p63 then fM n D (yx D j)∩fM n D (yf D j) else fM n D (yx D j)∪fM n D (yf D j):=by ext v;rw[w3,qu c _ j a];cases gZ D j<;>simp[w3]
lemma v9(h:fV n D)(K:tK)(c:K⊆inner n D)(a:∀j,j<(tD D)->n+j∈K->yx D j∈K\/yf D j∈K):(qc n D K).card+(w5 n D K).card=(z8 n K).card+q6 D K:=by obtain⟨p,q,-⟩:=h;have d:∀w∈K,w+1<n+(tD D):=λ w g=>ql.1 (c g);have J:q6 D K+K.card=((jw D).filter (λ e=>fC D e∈K)).card:=by{rw[<-zd p,yp (λ w g=>q w (d w g))]};have r:=p31 (s:=(jw D).filter (λ e=>fC D e∈K)) (λ e:tJ=>n+e.1∈K);rw[p38,p38] at r;have H:((jw D).filter (λ e=>fC D e∈K/\n+e.1∈K)).card=((g5 (tD D)).filter (λ j=>n+j∈K)).card+(w5 n D K).card:=by{rw[yo,w5,p30,p30,<-p50];refine p51 rfl (λ j l=>?_);have:=a j (mR.1 l);rw[qf,qo];by_cases m:n+j∈K<;>by_cases y:yx D j∈K<;>by_cases v:yf D j∈K<;>simp_all};have z:K.card=(z8 n K).card+((g5 (tD D)).filter (λ j=>n+j∈K)).card:=by{rw[<-p31 (s:=K) (λ w=>w<n),z8];congr 1;have i:K.filter (λ w=>¬w<n)=((g5 (tD D)).filter (λ j=>n+j∈K)).image (λ j=>n+j):=by{ext w;simp only[mF,mG,mR];exact⟨λ⟨g,u⟩=>⟨w-n,⟨by{have:=d w g;omega},by rwa[Nat.add_sub_cancel' (by omega)]⟩,by omega⟩,λ⟨j,⟨_,l⟩,h⟩=>⟨h▸l,by omega⟩⟩};rw[i,p33 _ (add_right_injective n)]};unfold qc;omega
lemma vt(T:tS n)(a:fM n D (qb n D)∩T=∅):q2 n D T⊆inner n D:=by intro w d;simp only[q2,mF,mR] at d;rw[ql];by_contra g;have c:w=qb n D:=by{unfold qb;omega};rw[c,a] at d;exact gk d.2
lemma jl(D:qD)(T:tS n):(z8 n (q2 n D T)).card=T.card:=by have c:z8 n (q2 n D T)=T.image (λ v:Fin n=>v.1):=by{ext w;simp only[z8,q2,mF,mR,mG];constructor;{rintro⟨⟨-,v,a⟩,d⟩;have g:fM n D w={⟨w,d⟩}:=wc D ⟨w,d⟩;rw[g,mI,mS] at a;exact⟨v,a.2,by rw[a.1]⟩};{rintro⟨v,a,rfl⟩;refine⟨⟨by have:=v.2;omega,v,?_⟩,v.2⟩;rw[wc];simp[a]}};rw[c,p33 _ Fin.val_injective]
lemma z4(h:fV n D)(T:tS n)(a:fM n D (qb n D)∩T=∅):(qc n D (q2 n D T)).card+(w5 n D (q2 n D T)).card=T.card+q6 D (q2 n D T):=by rw[<-jl D T];refine v9 h _ (vt T a) (λ j g i=>by{obtain⟨m,l,-⟩:=h.1 j g;simp only[q2,mF,mR] at i ⊢;obtain⟨v,c⟩:=i.2;rw[mI,yy h.1 j g] at c;split_ifs at c with ht;{rw[mI] at c;exact .inl ⟨by omega,v,mI.2 ⟨c.1.1,c.2⟩⟩};{rw[mN] at c;exact c.1.elim (λ d=>.inl ⟨by omega,v,mI.2 ⟨d,c.2⟩⟩) (λ d=>.inr ⟨by omega,v,mI.2 ⟨d,c.2⟩⟩)}})
lemma va(h:fV n D)(x y:Fin n)(c:x≠y)(a:x∉fM n D (qb n D)):(qc n D (q4 n D x y)).card+(w5 n D (q4 n D x y)).card=1+q6 D (q4 n D x y):=by have m:q4 n D x y⊆inner n D:=λ w i=>by{simp only[q4,mF,mR] at i;rw[ql];by_contra r;have:w=qb n D:=by{unfold qb;omega};exact a (this▸i.2.1)};have p:z8 n (q4 n D x y)={x.1}:=by{ext w;simp only[z8,q4,mF,mR,mS];exact⟨λ⟨⟨_,d,_⟩,i⟩=>by{rw[wc D ⟨w,i⟩,mS] at d;rw[d]},λ h=>h▸⟨⟨by{have:=x.2;omega},by{rw[wc];exact m0 x},by{rw[wc,mS];exact λ r=>c r.symm}⟩,x.2⟩⟩};have q:=v9 h _ m (λ j v z=>by{obtain⟨K,J,-⟩:=h.1 j v;simp only[q4,mF,mR] at z ⊢;obtain⟨-,d,g⟩:=z;rw[yy h.1 j v] at d g;split_ifs at d g with ht;{rw[mI] at d g;exact if l:y∈fM n D (yx D j) then .inr ⟨by omega,d.2,λ r=>g ⟨l,r⟩⟩ else .inl ⟨by omega,d.1,l⟩};{rw[mN] at d g;exact d.elim (λ u=>.inl ⟨by omega,u,λ r=>g (.inl r)⟩) (λ u=>.inr ⟨by omega,u,λ r=>g (.inr r)⟩)}});rwa[p,fw] at q
lemma xr{u:U0}:u∈units n D↔u.1∈inner n D/\u.2+1<fanout D u.1:=by rw[units,p44,mR];constructor<;>rintro⟨a,c⟩<;>exact⟨a,by omega⟩
lemma wh(n:Nat)(D:qD)(p:Nat->Prop) [DecidablePred p]:((units n D).filter (λ u=>p u.1)).card=q6 D ((inner n D).filter p):=by have a:(units n D).filter (λ u=>p u.1)=((inner n D).filter p).sigma (λ w=>g5 (fanout D w-1)):=by{ext u;simp only[units,mF,p44];tauto};rw[a,Finset.card_sigma,q6];simp
lemma k4(n:Nat)(D:qD):(ww n D).card=fJ n D:=by unfold ww fJ;exact wh n D (λ w=>(fM n D w).Nonempty)
lemma zz{v:Fin n}:v∈fX n D↔∃w,2<=fanout D w/\v∈fM n D w:=by simp only[fX,kl,mem_biUnion,mF,mR];constructor;{rintro⟨w,⟨-,c⟩,a⟩;exact⟨w,c,a⟩};{rintro⟨w,c,a⟩;refine⟨w,⟨?_,c⟩,a⟩;by_contra d;rw[xn D w (by omega)] at a;exact nE v a}
lemma zb{v:Fin n}:v∈ineligSet n D↔∀w,v∈fM n D w->fanout D w<=1:=by rw[ineligSet,mD,zz];constructor;{rintro⟨-,h⟩ w a;by_contra d;exact h ⟨w,by omega,a⟩};{intro h;refine⟨mU v,?_⟩;rintro⟨w,a,c⟩;have:=h w c;omega}
lemma wg{v:Fin n}{T:tS n}:(({v}:tS n)∩T).Nonempty↔v∈T:=by constructor;{rintro⟨u,a⟩;rw[mI,mS] at a;exact a.1▸a.2};{intro h;exact⟨v,mI.2 ⟨m0 v,h⟩⟩}
lemma zr(b:tY n)(a:gN n D b):Set.InjOn (λ v=>(⟨b v,0⟩:U0)) (fX n D:Set (Fin n)):=by intro v i g c j;have d:b v=b g:=congrArg Sigma.fst j;have h:=(a v i).2;rw[d,(a g c).2] at h;exact (p48 h).symm
lemma yl(c:q0 n D)(b:tY n)(a:gN n D b):qh n D b⊆ww n D:=by intro u g;obtain⟨v,d,rfl⟩:=mG.1 g;obtain⟨j,h⟩:=a v d;have i:1<=fanout D (b v):=by{omega};rw[ww,mF,xr];refine⟨⟨ql.2 (wk c i),?_⟩,?_⟩;{show 0+1<fanout D (b v);omega};{show (fM n D (b v)).Nonempty;rw[h];exact Finset.singleton_nonempty v}
lemma ke(b:tY n)(a:gN n D b):(qh n D b).card=(fX n D).card:=p32 (zr b a)
lemma kf(c:q0 n D)(b:tY n)(a:gN n D b):(residualUnits n D b).card+(fX n D).card=fJ n D:=by rw[<-ke b a,<-k4];exact p35 (yl c b a)
lemma jm(c:q0 n D)(b:tY n)(a:gN n D b)(T:tS n):q6 D (q2 n D T)=(T∩fX n D).card+((residualUnits n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)).card:=by have H:q6 D (q2 n D T)=((units n D).filter (λ u=>(fM n D u.1∩T).Nonempty)).card:=by{rw[wh n D (λ w=>(fM n D w∩T).Nonempty)];symm;refine sum_subset (λ w g=>by{rw[mF] at g;have:=ql.1 g.1;exact mF.2 ⟨mR.2 (by omega),g.2⟩}) (λ w g j=>by{rw[q2,mF] at g;have m:w∉inner n D:=λ hc=>j (mF.2 ⟨hc,g.2⟩);rw[ql] at m;simp[qz c w (by omega)]})};have z:(units n D).filter (λ u=>(fM n D u.1∩T).Nonempty)=(qh n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)∪(residualUnits n D b).filter (λ u=>(fM n D u.1∩T).Nonempty):=by{ext u;have i:=yl c b a;simp only[residualUnits,ww,mN,mF,mD];exact⟨λ d=>if p:u∈qh n D b then .inl ⟨p,d.2⟩ else .inr ⟨⟨⟨d.1,d.2.mono fI⟩,p⟩,d.2⟩,λ | .inl d=>⟨(mF.1 (i d.1)).1,d.2⟩ | .inr d=>⟨d.1.1.1,d.2⟩⟩};have r:(qh n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)=(T∩fX n D).image (λ v=>(⟨b v,0⟩:U0)):=by{rw[qh,Finset.filter_image];congr 1;ext v;simp only[mF,mI];exact⟨λ⟨h,l⟩=>⟨by rwa[(a v h).2,wg] at l,h⟩,λ⟨q,h⟩=>⟨h,by rwa[(a v h).2,wg]⟩⟩};rw[H,z,fU (Finset.disjoint_filter_filter (show Disjoint (qh n D b) (residualUnits n D b) from Finset.disjoint_sdiff)),r,p32 ((zr b a).mono (Finset.coe_subset.2 p40))]
end
def gL{n:Nat}(a:EP (Fin n))(w:Nat):Nat:=if h:w<n then (a ⟨w,h⟩).1 else w
def relabel {n:Nat}(a:EP (Fin n))(D:qD):qD:=D.map (λ g=>(g.1,gL a g.2.1,gL a g.2.2))
section
variable {n:Nat}(a:EP (Fin n))
include n a
lemma yh{w:Nat}(h:w<n):gL a w=(a ⟨w,h⟩).1:=by simp[gL,h]
lemma qt{w:Nat}(h:n<=w):gL a w=w:=by simp[gL,p25.2 h]
lemma qy{m:Nat}(c:n<=m)(w:Nat):gL a w<m↔w<m:=by by_cases h:w<n;{rw[yh a h];have:=(a ⟨w,h⟩).2;constructor<;>intro<;>omega};{rw[qt a (p25.1 h)]}
lemma yz(w:Nat):gL a⁻¹ (gL a w)=w:=by by_cases h:w<n;{rw[yh a h,yh a⁻¹ (a ⟨w,h⟩).2];simp};{rw[qt a (p25.1 h),qt a⁻¹ (p25.1 h)]}
lemma tr_liftP_inv'(w:Nat):gL a (gL a⁻¹ w)=w:=by simpa using yz a⁻¹ w
end
lemma tr_liftP_inj{n:Nat}(c:EP (Fin n)){a b:Nat}:gL c a=gL c b↔a=b:=by refine⟨λ h=>?_,congrArg _⟩;have:=congrArg (gL c⁻¹) h;rwa [yz,yz] at this
lemma relabel_length{n:Nat}(a:EP (Fin n))(D:qD):(relabel a D).length=(tD D):=by simp[relabel]
lemma ba{n:Nat}(c:EP (Fin n))(D:qD)(j:Nat)(a:j<(tD D)):gZ (relabel c D) j=gZ D j:=by rw[xd _ j (by rw[relabel_length];exact a),xd D j a];simp[relabel]
section
variable {n:Nat}(a:EP (Fin n))
include n a
lemma kt(D:qD)(j:Nat)(c:j<(tD D)):yx (relabel a D) j=gL a (yx D j):=by rw[xe _ j (by rw[relabel_length];exact c),xe D j c];simp[relabel]
lemma ku(D:qD)(j:Nat)(c:j<(tD D)):yf (relabel a D) j=gL a (yf D j):=by rw[xf _ j (by rw[relabel_length];exact c),xf D j c];simp[relabel]
lemma j3{D:qD}(c:q0 n D):q0 n (relabel a D):=by intro j d;rw[relabel_length] at d;obtain⟨l,i,g⟩:=c j d;rw[kt a D j d,ku a D j d];exact⟨(qy a (nL n j) _).2 l,(qy a (nL n j) _).2 i,λ h=>g ((tr_liftP_inj a).1 h)⟩
lemma fH{D:qD}(c:q0 n D)(x:tX n)(w:Nat):fO (relabel a D) x (gL a w)=fO D (λ i=>x (a i)) w:=by by_cases h:w<n+(tD D);{refine (jy (j3 a c) x (λ l=>fO D (λ i=>x (a i)) (gL a⁻¹ l)) (λ i g=>by{show fO D (λ i=>x (a i)) (gL a⁻¹ i)=x ⟨i,g⟩;rw[yh a⁻¹ g,qa D _ _ (a⁻¹ ⟨i,g⟩).2];simp}) (λ j d=>by{rw[relabel_length] at d;show fO D (λ i=>x (a i)) (gL a⁻¹ (n+j))=_;rw[qt a⁻¹ (nL n j),ba a D j d,kt a D j d,ku a D j d,yz,yz,qu c _ j d]}) (gL a w) (by{rw[relabel_length];exact (qy a (nL _ _) w).2 h})).trans (by{show fO D (λ i=>x (a i)) (gL a⁻¹ (gL a w))=_;rw[yz]})};{have hw':=p25.1 h;rw[qt a (le_trans (nL _ _) hw'),z0 _ _ _ (by{rw[relabel_length];exact hw'}),z0 _ _ _ hw']}
lemma wa(D:qD)(w:Nat):fanout (relabel a D) (gL a w)=fanout D w:=by unfold fanout qg;rw[relabel_length];congr 1;apply filter_congr;intro j c;have hj':=mR.1 c;rw[kt a D j hj',ku a D j hj',tr_liftP_inj,tr_liftP_inj]
lemma kv{D:qD}(c:b5 n D):b5 n (relabel a D):=by rcases eq_or_ne D [] with rfl|g;{exact c};{intro d j;rw[relabel_length] at j;have i:=lP g;rw[<-tr_liftP_inv' a d,wa];apply c;by_cases h:d<n;{have:=(qy a⁻¹ le_rfl d).2 h;omega};{rw[qt a⁻¹ (p25.1 h)];exact j}}
lemma relabel_strictLive{D:qD}(h:fV n D):fV n (relabel a D):=⟨j3 a h.1,kv a h.2.1,by simpa[relabel] using h.2.2⟩
lemma xa{D:qD}(d:q0 n D)(c:D≠[])(x:tX n):fO (relabel a D) x (qb n (relabel a D))=fO D (λ i=>x (a i)) (qb n D):=by have g:=lP c;have e:qb n (relabel a D)=gL a (qb n D):=by{rw[qt a (by unfold qb;omega)];simp[qb,relabel_length]};rw[e,fH a d]
lemma k5(v:Fin n):(λ i=>q9 v (a i))=q9 (a⁻¹ v):=by funext i;simp only[q9,decide_eq_decide];constructor;{intro h;rw[<-h];simp};{intro h;rw[h];simp}
end
lemma relabel_supp{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D)(w:Nat):fM n (relabel c D) (gL c w)=(fM n D w).image c:=by ext v;simp only[fM,mF,mU,true_and,mG];rw[fH c d,k5];constructor;{intro h;exact⟨c⁻¹ v,h,by simp⟩};{rintro⟨a,g,rfl⟩;simpa using g}
namespace A0r
abbrev rL:=@relabel_length
abbrev rS:=@relabel_supp
abbrev tI:=@tr_liftP_inv'
abbrev gq:=@tr_liftP_inj
end A0r
open A0r
lemma ym{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D):fX n (relabel c D)=(fX n D).image c:=by ext v;simp only[fX,mem_biUnion,mG,kl,mF,mR];constructor;{rintro⟨h,⟨hw',g⟩,j⟩;obtain⟨w,rfl⟩:∃w,h=gL c w:=⟨gL c⁻¹ h,(tI c h).symm⟩;rw[rS c d,mG] at j;obtain⟨a,i,rfl⟩:=j;rw[wa] at g;rw[rL,qy c (nL _ _)] at hw';exact⟨a,⟨w,⟨hw',g⟩,i⟩,rfl⟩};{rintro⟨a,⟨w,⟨l,g⟩,i⟩,rfl⟩;refine⟨gL c w,⟨?_,?_⟩,?_⟩;{rw[rL];exact (qy c (nL _ _) w).2 l};{rw[wa];exact g};{rw[rS c d];exact Finset.mem_image_of_mem _ i}}
lemma relabel_ineligSet{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D):ineligSet n (relabel c D)=(ineligSet n D).image c:=by ext v;simp only[ineligSet,ym c d,mD,mU,true_and,mG];constructor;{intro h;exact⟨c⁻¹ v,λ i=>h ⟨c⁻¹ v,i,by simp⟩,by simp⟩};{rintro⟨a,l,rfl⟩ ⟨b,j,g⟩;exact l (c.injective g▸j)}
lemma vu(n:Nat)(D:qD):(ineligSet n D).card+(fX n D).card=n:=by have h:=p35 (Finset.subset_univ (fX n D));rw[Finset.card_univ,Fintype.card_fin] at h;exact h
def yi{n:Nat}(G:Fin n->Fin n->Prop)(x:tX n):Prop:=∃u v:Fin n,G u v/\x u=p63/\x v=p63
def gK(n:Nat)(G:Fin n->Fin n->Prop)(D:qD):Prop:=∀x:tX n,fO D x (qb n D)=p63↔yi G x
abbrev sem_Comp:=gK
def w6{n:Nat}(G:Fin n->Fin n->Prop):Prop:=(∀u v,G u v->G v u)/\(∀u,¬G u u)/\(∀v w,v≠w->∃z,G v z/\¬G w z)/\(∀u v,∃a,G u a/\a≠v)
def q5(n:Nat)(D:qD)(a b:Nat):Prop:=b<n+(tD D)/\n<=b/\(yx D (b-n)=a\/yf D (b-n)=a)
def q1{n:Nat}(u z:Fin n):tX n:=λ i=>decide (i=u)||decide (i=z)
def wm{n:Nat}(v:Fin n)(x:tX n):tX n:=λ i=>decide (i=v)||x i
def yc{n:Nat}(A:tS n):tX n:=λ i=>decide (i∈A)
lemma yu{α:Type}{r p:α->α->Prop}(h:∀a b,r a b->p a b){a b:α}(c:RT r a b):RT p a b:=by induction c with|refl=>{exact .refl}|tail _ d ih=>{exact rT ih (h _ _ d)}
section
variable {n:ℕ} {G:Fin n->Fin n->Prop} {D:qD}
lemma jr(v:Fin n)(x:tX n):∀k,k≠v->x k=wm v x k:=by intro k c;simp[wm,c]
lemma vb(v:Fin n)(x:tX n):wm v x v=p63:=by simp[wm]
lemma kg{x:tX n}{u:Fin n}(a:x u=p63):∀i,q9 u i=p63->x i=p63:=by intro i c;simp only[q9,dT] at c;rw[c];exact a
lemma q3(d:q0 n D){u:Fin n}{w:Nat}(c:u∈fM n D w){x:tX n}(a:x u=p63):fO D x w=p63:=x9 d (q9 u) x (kg a) w (w3.1 c)
lemma wx{v:Fin n}{w:Nat}(a:v∈fM n D w):w<n+(tD D):=by by_contra c;rw[xn D w (by omega)] at a;exact nE v a
section
variable (Q:q0 n D){j:Nat}(A:j<(tD D))
include Q j A
lemma qm(d:gZ D j=p63):fM n D (n+j)=fM n D (yx D j)∩fM n D (yf D j):=by rw[yy Q j A];simp[d]
lemma yj(d:gZ D j=p55):fM n D (n+j)=fM n D (yx D j)∪fM n D (yf D j):=by rw[yy Q j A];simp[d]
lemma sem_supp_and_sub(d:gZ D j=p63)(s:Bool):fM n D (n+j)⊆fM n D (fC D (j,s)):=by rw[qm Q A d];cases s;{rw[qf];exact fI};{rw[qo];exact p40}
lemma w7(s:Bool):fC D (j,s)<n+j:=by obtain⟨g,d,-⟩:=Q j A;cases s;{rw[qf];exact g};{rw[qo];exact d}
lemma xj(s:Bool):fC D (j,s)≠fC D (j,!s):=by obtain⟨-,-,d⟩:=Q j A;cases s;{simpa[fC] using d};{simpa[fC] using d.symm}
end
lemma qs{j:Nat}(a:j<(tD D))(s:Bool):q5 n D (fC D (j,s)) (n+j):=by refine⟨by omega,by omega,?_⟩;rw[nA];cases s;{exact .inl (qf j).symm};{exact .inr (qo j).symm}
lemma y3{a b:Nat}:q5 n D a b↔∃j s,j<(tD D)/\b=n+j/\fC D (j,s)=a:=by constructor;{rintro⟨h,g,c|c⟩;{exact⟨b-n,p55,by omega,by omega,by rw[qf];exact c⟩};{exact⟨b-n,p63,by omega,by omega,by rw[qo];exact c⟩}};{rintro⟨j,s,d,rfl,rfl⟩;refine⟨by omega,by omega,?_⟩;rw[nA];cases s;{exact .inl (qf j).symm};{exact .inr (qo j).symm}}
lemma wb(c:q0 n D){a b:Nat}(h:q5 n D a b):a<b:=by obtain⟨i,g,d⟩:=h;have:=c (b-n) (by omega);omega
lemma wr{a c:Nat}(h:q5 n D a c):c-n∈qg D a:=by unfold qg;rw[mF,mR];exact⟨by have:=h.1;have:=h.2.1;omega,h.2.2⟩
lemma zs{a c:Nat}(h:q5 n D a c):1<=fanout D a:=fz.2 ⟨_,wr h⟩
lemma qj{a c h:Nat}(g:q5 n D a c)(d:q5 n D a h)(i:fanout D a=1):c=h:=by have l:=wr g;have j:=wr d;obtain⟨r,m⟩:=p29.1 (show (qg D a).card=1 from i);rw[m,mS] at l j;have:=g.2.1;have:=d.2.1;omega
lemma wn(g:q0 n D)(x y:tX n)(v:Fin n)(d:∀k,k≠v->x k=y k)(w:Nat)(c:fO D x w≠fO D y w):RT (λ a b=>q5 n D a b/\fO D x b≠fO D y b) v.1 w:=by induction w using sI with|_ w ih=>{by_cases l:w<n;{rw[qa D x w l,qa D y w l] at c;have i:(⟨w,l⟩:Fin n)=v:=by_contra λ hc=>c (d _ hc);rw[<-i]};{by_cases h:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have m:j<(tD D):=by{omega};obtain⟨z,u,-⟩:=g j m;have q:=c;rw[qu g x j m,qu g y j m] at q;by_cases r:fO D x (yx D j)=fO D y (yx D j);exact rT (ih _ u λ p=>q (by rw[r,p])) ⟨⟨h,by omega,.inr (by rw[nA])⟩,c⟩;exact rT (ih _ z r) ⟨⟨h,by omega,.inl (by rw[nA])⟩,c⟩};{exact absurd (by rw[z0 D x w (by omega),z0 D y w (by omega)]) c}}}
def kw(n:Nat)(D:qD)(b v:Nat):Prop:=b=v\/¬RT (λ a c=>q5 n D a c/\c≠b) v (qb n D)
lemma k6(j:q0 n D)(x y:tX n)(v:Fin n)(g:∀k,k≠v->x k=y k)(b:Nat)(d:kw n D b v.1)(i:fO D x b=fO D y b):fO D x (qb n D)=fO D y (qb n D):=by by_contra m;rcases d with rfl|d;{rw[qa D x _ v.2,qa D y _ v.2] at i;exact m (congrArg (λ f=>fO D f (qb n D)) (funext λ k=>if hk:k=v then hk▸i else g k hk))};{exact d (yu (λ _ _ h=>⟨h.1,λ hc=>h.2 (hc▸i)⟩) (wn j x y v g _ m))}
def q7(n:Nat)(D:qD)(a b:Nat):Prop:=RT (λ a c=>q5 n D a c/\fanout D a=1) a b
lemma wp(d:q0 n D){v b:Nat}(h:q7 n D v b):kw n D b v:=by induction h using rI with|refl=>{exact .inl rfl}|@head a c g _ ih=>{by_cases m:b=a;{exact .inl m};{right;intro q;rcases rC q with j|⟨r,p,i⟩;{have y:=qz d a (by rw[j];unfold qb;omega);have u:=g.2;omega};{have l:c=r:=qj g.1 p.1 g.2;subst l;rcases ih with rfl|ih;{exact p.2 rfl};{exact ih i}}}}
lemma z9(a:q0 n D)(v:Fin n):∀w,v∈fM n D w->(∀u,u<w->v∈fM n D u->fanout D u<=1)->q7 n D v.1 w:=by intro w;induction w using sI with|_ w ih=>{intro h d;by_cases p:w<n;{have:=wc D ⟨w,p⟩;rw[this,mS] at h;rw[h];exact .refl};{have r:=wx h;obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have m:j<(tD D):=by{omega};have g:∀s:Bool,v∈fM n D (fC D (j,s))->q7 n D v.1 (n+j):=λ s i=>by{have c:q5 n D (fC D (j,s)) (n+j):=qs m s;have hlt':=w7 a m s;have:=zs c;have:=d _ hlt' i;exact rT (ih _ hlt' i (λ u y=>d u (by omega))) ⟨c,by omega⟩};rw[yy a j m] at h;split_ifs at h with ht;exact g p55 (by{rw[qf];exact (mI.1 h).1});rcases mN.1 h with l|l;exact g p55 (by{rw[qf];exact l});exact g p63 (by{rw[qo];exact l})}}
lemma wd(d:w6 G)(v:Fin n):¬yi G (q9 v):=by rintro⟨a,c,g,h,hc⟩;simp only[q9,dT] at h hc;rw[h,hc] at g;exact d.2.1 _ g
lemma yv{u v:Fin n}(a:G u v):yi G (q1 u v):=⟨u,v,a,by simp[q1],by simp[q1]⟩
lemma qn(a:w6 G)(c:gK n G D):fM n D (qb n D)=∅:=fE.2 (λ v d=>wd a v ((c _).1 (w3.1 d)))
lemma yw(i:w6 G)(g:q0 n D)(h:gK n G D)(v:Fin n)(b:Nat)(d:kw n D b v.1):fM n D b⊆{v}:=by intro u M;rw[mS];by_contra L;obtain⟨p,l,q,-⟩:=i;obtain⟨z,K,m⟩:=q v u (Ne.symm L);have r:=k6 g _ _ v (jr v (q1 u z)) b d (by rw[q3 g M (by simp[q1]),q3 g M (by simp[wm,q1])]);have P:=(h (wm v (q1 u z))).2 ⟨v,z,K,vb v _,by simp[wm,q1]⟩;rw[<-r] at P;obtain⟨a,c,j,y,hc⟩:=(h _).1 P;simp only[q1,bO,dT] at y hc;rcases y with rfl|rfl<;>rcases hc with rfl|rfl;{exact l _ j};{exact m j};{exact m (p _ _ j)};{exact l _ j}
lemma vl(d:w6 G)(a:q0 n D)(g:gK n G D)(v:Fin n)(c:v∈fX n D):∃b,2<=fanout D b/\fM n D b={v}/\q7 n D v.1 b:=by classical have h:∃w,2<=fanout D w/\v∈fM n D w:=zz.1 c;obtain⟨p,l⟩:=p24 h;have i:q7 n D v.1 (p22 h):=z9 a v _ l (λ u m j=>by{have:=p23 h m;by_contra q;exact this ⟨by omega,j⟩});exact⟨p22 h,p,Finset.Subset.antisymm (yw d a g v _ (wp a i)) (p49.2 l),i⟩
def zt(n:Nat)(D:qD)(b:tY n):Prop:=∀v∈fX n D,2<=fanout D (b v)/\fM n D (b v)={v}/\q7 n D v.1 (b v)
lemma zj(c:w6 G)(a:q0 n D)(d:gK n G D):∃b:tY n,zt n D b:=by classical have h:∀v:Fin n,∃b,v∈fX n D->2<=fanout D b/\fM n D b={v}/\q7 n D v.1 b:=by{intro v;by_cases g:v∈fX n D;{obtain⟨b,i⟩:=vl c a d v g;exact⟨b,λ _=>i⟩};{exact⟨0,λ h=>absurd h g⟩}};choose b i using h;exact⟨b,λ v g=>i v g⟩
lemma j4{b:tY n}(a:zt n D b):gN n D b:=λ v c=>⟨(a v c).1,(a v c).2.1⟩
lemma sem_exists_pureBranch(c:w6 G)(a:q0 n D)(d:gK n G D):∃b:tY n,gN n D b:=by obtain⟨b,g⟩:=zj c a d;exact⟨b,j4 g⟩
lemma sem_mem_inelig{v:Fin n}:v∈ineligSet n D↔v∉fX n D:=by simp[ineligSet]
lemma vm(d:q0 n D){v:Fin n}(c:v∈ineligSet n D){w:Nat}(a:v∈fM n D w):q7 n D v.1 w:=z9 d v w a (λ u _ g=>zb.1 c u g)
lemma sem_inelig_pure(g:w6 G)(a:q0 n D)(h:gK n G D){v:Fin n}(d:v∈ineligSet n D){w:Nat}(c:v∈fM n D w):fM n D w={v}:=Finset.Subset.antisymm (yw g a h v w (wp a (vm a d c))) (p49.2 c)
lemma q8{v:Fin n}{w:Nat}:w∈q2 n D {v}↔v∈fM n D w:=by simp only[q2,mF,mR];constructor;{rintro⟨-,u,a⟩;rw[mI,mS] at a;exact a.2▸a.1};{intro h;exact⟨wx h,v,mI.2 ⟨h,m0 v⟩⟩}
lemma we{v:Fin n}{e:tJ}:e∈qc n D (q2 n D {v})↔e.1<(tD D)/\v∈fM n D (fC D e)/\v∉fM n D (n+e.1):=by simp only[qc,jw,mF,mem_product,mR,mU,and_true,q8]
lemma v1{v:Fin n}(a:v∈ineligSet n D):q6 D (q2 n D {v})=0:=by unfold q6;refine p52 (λ w c=>?_);have:=zb.1 a w (q8.1 c);omega
lemma y4(i:w6 G)(c:q0 n D)(g:gK n G D){u v:Fin n}(d:G u v):∃j,j<(tD D)/\gZ D j=p63/\fO D (q1 u v) (n+j)=p63/\u∉fM n D (n+j)/\v∉fM n D (n+j)/\∃s:Bool,u∈fM n D (fC D (j,s))/\v∉fM n D (fC D (j,s))/\v∈fM n D (fC D (j,!s))/\u∉fM n D (fC D (j,!s)):=by classical have y:∃w,fO D (q1 u v) w=p63/\u∉fM n D w/\v∉fM n D w:=⟨qb n D,(g _).2 (yv d),by{rw[qn i g];simp},by{rw[qn i g];simp}⟩;obtain⟨l,p,m⟩:=p24 y;have q:∀a,a<p22 y->fO D (q1 u v) a=p63->u∈fM n D a\/v∈fM n D a:=λ a Q R=>by_contra λ hc=>by{rw[not_or] at hc;exact p23 y Q ⟨R,hc.1,hc.2⟩};generalize p22 y=w at l p m q;have Y:w<n+(tD D):=by{by_contra hc;rw[z0 D _ w (by omega)] at l;cases l};have Z:n<=w:=by{by_contra hc;rw[qa D _ w (by omega)] at l;have X:fM n D w={⟨w,by omega⟩}:=wc D ⟨w,by omega⟩;rw[X,mS] at p m;simp only[q1,bO,dT] at l;rcases l with h|h;exact p h.symm;exact m h.symm};obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have J:j<(tD D):=by{omega};obtain⟨Q,U,-⟩:=c j J;have H:=l;have A:=p;have B:=m;rw[qu c _ j J] at l;rw[yy c j J] at p m;cases ht:gZ D j;{rw[ht] at l p m;simp only[gop_false,bO] at l;simp only[bF,ite_false,mN,not_or] at p m;rcases l with h|h;{rcases q _ Q h with z|z;exact (p.1 z).elim;exact (m.1 z).elim};{rcases q _ U h with z|z;exact (p.2 z).elim;exact (m.2 z).elim}};{rw[ht] at l p m;simp only[gop_true,bA] at l;simp only[ite_true,mI,not_and] at p m;refine⟨j,J,ht,H,A,B,?_⟩;rcases q _ Q l.1 with P|P;{have M:=p P;have K:=(q _ U l.2).resolve_left M;exact⟨p55,P,λ h=>m h K,K,M⟩};{have M:=m P;have L:=(q _ U l.2).resolve_right M;exact⟨p63,L,M,P,λ h=>p h L⟩}}
lemma qe(c:w6 G)(h:fV n D)(d:gK n G D){v:Fin n}(g:v∈ineligSet n D):∃e:tJ,e.1<(tD D)/\gZ D e.1=p63/\fM n D (fC D e)={v}/\fM n D (n+e.1)=∅/\(∀a,G v a->a∈fM n D (fC D (e.1,!e.2)))/\qc n D (q2 n D {v})={e}/\w5 n D (q2 n D {v})=∅:=by have R:=h.1;have P:=z4 h {v} (by{rw[qn c d];simp});rw[v1 g,fw] at P;have i:∀a,G v a->∃j s,j<(tD D)/\gZ D j=p63/\(j,s)∈qc n D (q2 n D {v})/\a∈fM n D (fC D (j,!s)):=λ a m=>by{obtain⟨j,X,ht,-,M,-,s,h1,-,Z,-⟩:=y4 c R d m;exact⟨j,s,X,ht,we.2 ⟨X,h1,M⟩,Z⟩};obtain⟨a0,Q,-⟩:=c.2.2.2 v v;obtain⟨K,s0,H,u,p,-⟩:=i a0 Q;have q:(qc n D (q2 n D {v})).card=1:=by{have:=fz.2 ⟨_,p⟩;omega};obtain⟨e,J⟩:=p29.1 q;rw[J,mS] at p;subst p;have M:=we.1 (J▸m0 _);have l:fM n D (fC D (K,s0))={v}:=sem_inelig_pure c R d g M.2.1;exact⟨(K,s0),H,u,l,p37 (λ x U=>M.2.2 ((mS.1 (l▸sem_supp_and_sub R H u s0 U))▸U)),λ a m=>by{obtain⟨j,s,-,-,L,Y⟩:=i a m;rw[J,mS,Prod.mk.injEq] at L;obtain⟨rfl,rfl⟩:=L;exact Y},J,g8.1 (by omega)⟩
lemma j5(c:w6 G)(h:fV n D)(g:gK n G D){u v:Fin n}(d:G u v):u∈fX n D\/v∈fX n D:=by by_contra hc;rw[not_or] at hc;obtain⟨R,-,-,-,-,q,l,-⟩:=qe c h g (sem_mem_inelig.2 hc.1);obtain⟨Q,-,-,p,-,-,i,-⟩:=qe c h g (sem_mem_inelig.2 hc.2);obtain⟨j,K,-,-,y,r,s,P,-,M,-⟩:=y4 c h.1 g d;have J:(j,s)∈qc n D (q2 n D {u}):=we.2 ⟨K,P,y⟩;have H:(j,!s)∈qc n D (q2 n D {v}):=we.2 ⟨K,M,r⟩;rw[l,mS] at J;rw[i,mS] at H;subst J;subst H;obtain⟨a,m,z⟩:=c.2.2.2 u v;have L:a∈fM n D (fC D (j,!s)):=q a m;rw[p,mS] at L;exact z L
lemma vv{A:tS n}(d:∀a∈A,∀b∈A,¬G a b):¬yi G (yc A):=by rintro⟨a,c,g,h,hc⟩;simp only[yc,dT] at h hc;exact d a h c hc g
lemma vc(h:w6 G)(c:q0 n D)(g:gK n G D)(A:tS n)(i:∀a∈A,∀b∈A,¬G a b)(x:Fin n)(d:∃a∈A,G x a):∃j s,j<(tD D)/\gZ D j=p63/\x∈fM n D (fC D (j,s))/\x∉fM n D (n+j)/\Disjoint (fM n D (fC D (j,s))) A:=by by_contra H;have m:∀j s,j<(tD D)->gZ D j=p63->x∈fM n D (fC D (j,s))->x∉fM n D (n+j)->fO D (yc A) (fC D (j,s))=p63/\fO D (wm x (yc A)) (fC D (j,s))=p63:=λ j s p y q R=>by{obtain⟨a,K,J⟩:=Finset.not_disjoint_iff.1 (λ Z=>H ⟨j,s,p,y,q,R,Z⟩);exact⟨q3 c K (by simp[yc,J]),q3 c K (by simp[wm,yc,J])⟩};have P:∀w,x∉fM n D w->fO D (yc A) w=fO D (wm x (yc A)) w:=λ w=>by{induction w using sI with|_ w ih=>{intro r;by_cases M:w<n;{rw[qa D _ w M,qa D _ w M];rw[wc D ⟨w,M⟩,mS] at r;exact jr x _ _ (λ hc=>r hc.symm)};by_cases Y:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have p:j<(tD D):=by{omega};obtain⟨L,Q,-⟩:=c j p;rw[qu c _ j p,qu c _ j p];cases y:gZ D j;{rw[yj c p y,mN,not_or] at r;rw[ih _ L r.1,ih _ Q r.2]};{have v:=r;rw[qm c p y,mI,not_and] at v;by_cases l:x∈fM n D (yx D j);{have q:=m j p55 p y (l) r;rw[qf] at q;rw[ih _ Q (v l),q.1,q.2]};by_cases u:x∈fM n D (yf D j);{have q:=m j p63 p y (u) r;rw[qo] at q;rw[ih _ L l,q.1,q.2]};{rw[ih _ L l,ih _ Q u]}}};{rw[z0 D _ w (by omega),z0 D _ w (by omega)]}}};obtain⟨a,L,l⟩:=d;exact vv i ((g _).1 (P (qb n D) (qn h g▸nE x)▸(g _).2 ⟨x,a,l,vb x _,by simp[wm,yc,L]⟩))
def fD(n:Nat)(D:qD)(x:Fin n):tF (tJ):=qc n D (q2 n D {x})
def sem_bar (e:Nat×Bool):Nat×Bool:=(e.1,!e.2)
lemma sem_mem_W{x:Fin n}{e:tJ}:e∈fD n D x↔e.1<(tD D)/\x∈fM n D (fC D e)/\x∉fM n D (n+e.1):=we
lemma sem_bar_bar(e:tJ):sem_bar (sem_bar e)=e:=by simp[sem_bar]
lemma sem_same_gate{e f:tJ}(h:e.1=f.1):f=e\/f=sem_bar e:=by obtain⟨j,s⟩:=e;obtain⟨k,t⟩:=f;simp only at h;subst h;cases s<;>cases t<;>simp[sem_bar]
lemma sem_W_and(c:q0 n D){x:Fin n}{e:tJ}(a:e∈fD n D x):gZ D e.1=p63:=by obtain⟨g,d,h⟩:=sem_mem_W.1 a;by_contra i;rw[Bool.not_eq_true] at i;apply h;rw[yj c g i,mN];obtain⟨j,s⟩:=e;cases s;{left;simpa[fC] using d};{right;simpa[fC] using d}
namespace A0b
abbrev sM:=@sem_mem_W
abbrev sA:=@sem_W_and
abbrev sP:=@sem_inelig_pure
abbrev sU:=@sem_supp_and_sub
abbrev sE:=@sem_mem_inelig
lemma sK{g:Nat}{s:Bool}:sem_bar (g,!s)=(g,s):=by cases s<;>rfl
lemma sX{D:qD}{g w:Nat}(h:yx D g=w\/yf D g=w):∃s,fC D (g,s)=w:=h.elim (λ h=>⟨p55,h⟩) (λ h=>⟨p63,h⟩)
end A0b
open A0b
lemma xt(a:w6 G)(h:fV n D)(c:gK n G D)(x:Fin n):(fD n D x).card+(w5 n D (q2 n D {x})).card=1+q6 D (q2 n D {x}):=by have d:=z4 h {x} (by rw[qn a c];simp);rwa [fw] at d
lemma z5(d:w6 G)(c:q0 n D)(g:gK n G D){x y:Fin n}(a:G x y):∃e,e∈fD n D x/\sem_bar e∈fD n D y/\y∉fM n D (fC D e)/\x∉fM n D (fC D (sem_bar e))/\fO D (q1 x y) (n+e.1)=p63:=by obtain⟨j,m,-,h,l,i,s,u,r,q,p⟩:=y4 d c g a;exact⟨(j,s),sM.2 ⟨m,u,l⟩,sM.2 ⟨m,q,i⟩,r,p,h⟩
lemma qk(c:q0 n D){R:Nat->Nat->Prop}(d:∀a b,R a b->q5 n D a b){a b:Nat}(h:RT R a b):a<=b:=by induction h with|refl=>{exact le_refl _}|tail _ g ih=>{exact le_trans ih (le_of_lt (wb c (d _ _ g)))}
lemma j6(d:q0 n D){x:Fin n}(g:w5 n D (q2 n D {x})=∅){j:Nat}(c:j<(tD D))(a:x∈fM n D (n+j)):gZ D j=p55/\¬(x∈fM n D (yx D j)/\x∈fM n D (yf D j)):=by have h:¬(x∈fM n D (yx D j)/\x∈fM n D (yf D j)):=by{intro m;have i:j∈w5 n D (q2 n D {x}):=by{rw[w5,mF,mR];exact⟨c,q8.2 a,q8.2 m.1,q8.2 m.2⟩};rw[g] at i;exact nE _ i};refine⟨?_,h⟩;by_contra l;rw[p59] at l;rw[qm d c l,mI] at a;exact h a
lemma j7(c:w6 G)(h:fV n D)(d:gK n G D)(b:tY n)(a:gN n D b)(x:Fin n):(fD n D x).card+(w5 n D (q2 n D {x})).card=1+(({x}:tS n)∩fX n D).card+((residualUnits n D b).filter (λ u=>x∈fM n D u.1)).card:=by have m:=xt c h d x;have l:=jm h.1 b a {x};have j:(residualUnits n D b).filter (λ u=>(fM n D u.1∩{x}).Nonempty)=(residualUnits n D b).filter (λ u=>x∈fM n D u.1):=by{refine filter_congr (λ u _=>?_);constructor;{rintro⟨y,g⟩;rw[mI,mS] at g;exact g.2▸g.1};{intro i;exact⟨x,mI.2 ⟨i,m0 x⟩⟩}};rw[j] at l;omega
section
variable (Q:q0 n D)
include Q
lemma qd(x:tX n){j:Nat}(a:j<(tD D))(s:Bool):fO D x (n+j)=xp (gZ D j) (fO D x (fC D (j,s))) (fO D x (fC D (j,!s))):=by rw[qu Q x j a];cases s;{simp[fC]};{cases gZ D j<;>simp[fC,Bool.and_comm,Bool.or_comm]}
lemma vn{v b t:Nat}(h:q7 n D v b)(g:b<=t):b=v\/¬RT (λ a c=>q5 n D a c/\c≠b) v t:=by induction h using rI with|refl=>{exact .inl rfl}|@head a c i l ih=>{by_cases p:b=a;{exact .inl p};{right;intro u;rcases rC u with y|⟨z,r,j⟩;{have J:=wb Q i.1;have H:=qk Q (λ _ _ q=>q.1) l;omega};{have m:c=z:=qj i.1 r.1 i.2;subst m;rcases ih with rfl|ih;{exact r.2 rfl};{exact ih j}}}}
lemma kh(x y:tX n)(v:Fin n)(g:∀k,k≠v->x k=y k)(b t:Nat)(d:b=v.1\/¬RT (λ a c=>q5 n D a c/\c≠b) v.1 t)(i:fO D x b=fO D y b):fO D x t=fO D y t:=by by_contra m;rcases d with rfl|d;{rw[qa D x _ v.2,qa D y _ v.2] at i;have l:x=y:=by{funext k;by_cases p:k=v;{rw[p];exact i};{exact g k p}};exact m (by rw[l])};{exact d (yu (λ a c h=>⟨h.1,λ hc=>h.2 (by rw[hc];exact i)⟩) (wn Q x y v g _ m))}
lemma j8{a c q:Nat}(hc:q7 n D a c)(d:RT (q5 n D) a q):RT (q5 n D) c q\/(q7 n D q c/\q≠c):=by revert d;induction hc using rI with|refl=>{exact λ d=>.inl d}|@head a v h i ih=>{intro d;rcases rC d with l|⟨r,u,j⟩;{right;have z:=wb Q h.1;have y:=qk Q (λ _ _ p=>p.1) i;refine⟨?_,by omega⟩;rw[<-l];exact rH h i};{have m:v=r:=qj h.1 u h.2;subst m;exact ih j}}
lemma vd(v:Fin n){j:Nat}(c:j<(tD D))(s:Bool)(g:q7 n D v.1 (fC D (j,!s)))(i:fanout D (fC D (j,!s))=1)(x y:tX n)(d:∀k,k≠v->x k=y k):fO D x (fC D (j,s))=fO D y (fC D (j,s)):=by by_contra z;have M:=yu (λ _ _ h=>h.1) (wn Q x y v d _ z);have:=w7 Q c s;have:=w7 Q c (!s);rcases j8 Q g M with H|⟨H,P⟩;{rcases rC H with q|⟨A,u,l⟩;exact xj Q c s q.symm;have r:=qj (qs c (!s)) u i;subst r;have:=qk Q (λ _ _ h=>h) l;omega};{rcases rC H with q|⟨L,u,l⟩;exact P q;have r:=qj (qs c s) u.1 u.2;subst r;have:=qk Q (λ _ _ h=>h.1) l;omega}
end
lemma ze(g:w6 G)(c:q0 n D)(h:gK n G D){i:Fin n}(d:i∈ineligSet n D){b:Nat}(a:q7 n D i.1 b)(j:2<=fanout D b):fM n D b=∅:=by have l:=yw g c h i b (wp c a);refine p37 (λ x m=>?_);have p:=l m;rw[mS] at p;have q:=zb.1 d b (p▸m);omega
lemma j9{a t:Nat}(c:RT (q5 n D) a t):q7 n D a t\/∃b,q7 n D a b/\2<=fanout D b:=by induction c using rI with|refl=>{exact .inl rR}|@head a j d _ ih=>{by_cases h:fanout D a=1;{rcases ih with g|⟨b,g,i⟩;{exact .inl (rH ⟨d,h⟩ g)};{exact .inr ⟨b,rH ⟨d,h⟩ g,i⟩}};{have:=zs d;exact .inr ⟨a,rR,by omega⟩}}
lemma yd(c:q0 n D){b:Nat}(d:2<=fanout D b)(a:fM n D b=∅):b∈(inner n D).filter (λ w=>¬(fM n D w).Nonempty):=mF.2 ⟨ql.2 (wk c (w:=b) (by omega)),by rw[a];exact gk⟩
lemma y7(d:q0 n D)(a:Bzero n D=0){b:Nat}(c:2<=fanout D b):(fM n D b).Nonempty:=by by_contra g;rw[fN] at g;have h:fanout D b-1<=∑ w∈(inner n D).filter (λ w=>¬(fM n D w).Nonempty),(fanout D w-1):=hE (f:=λ w=>fanout D w-1) (λ _ _=>nZ _) (yd d c g);unfold Bzero q6 at a;omega
section
variable (K:w6 G)(H:fV n D)(C:gK n G D)(B:Bzero n D=0){i:Fin n}(M:i∈ineligSet n D)
include K H C B i M
lemma v3{w:Nat}(c:RT (q5 n D) i.1 w):q7 n D i.1 w:=by rcases j9 c with l|⟨b,l,p⟩;{exact l};{have m:=y7 H.1 B p;rw[ze K H.1 C M l p] at m;exact absurd m gk}
lemma zv:q7 n D i.1 (qb n D):=v3 K H C B M (vk H i.1 (by have:=i.2;omega))
end
lemma zk{x y:Fin n}{w:Nat}:w∈q4 n D x y↔x∈fM n D w/\y∉fM n D w:=by simp only[q4,mF,mR];exact⟨λ h=>h.2,λ h=>⟨wx h.1,h⟩⟩
lemma y5{x y:Fin n}{e:tJ}:e∈qc n D (q4 n D x y)↔e.1<(tD D)/\(x∈fM n D (fC D e)/\y∉fM n D (fC D e))/\¬(x∈fM n D (n+e.1)/\y∉fM n D (n+e.1)):=by simp only[qc,jw,mF,mem_product,mR,mU,and_true,zk]
lemma vp(g:q0 n D)(b:tY n)(d:gN n D b){x y:Fin n}(a:x≠y)(c:x∈fX n D):q6 D (q4 n D x y)=1+((residualUnits n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)).card:=by have K:q6 D (q4 n D x y)=((units n D).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)).card:=by{rw[wh n D (λ w=>x∈fM n D w/\y∉fM n D w)];symm;refine sum_subset (λ w p=>zk.2 (mF.1 p).2) (λ w p l=>by{have q:w∉inner n D:=λ hc=>l (mF.2 ⟨hc,zk.1 p⟩);rw[ql] at q;simp[qz g w (by omega)]})};have J:(units n D).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)={(⟨b x,0⟩:U0)}∪(residualUnits n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1):=by{ext u;have j:=yl g b d;simp only[residualUnits,ww,mN,mF,mD,mS];exact⟨λ h=>if r:u∈qh n D b then .inl (by{obtain⟨v,z,rfl⟩:=mG.1 r;have i:=h.2.1;rw[(d v z).2,mS] at i;rw[i]}) else .inr ⟨⟨⟨h.1,⟨x,h.2.1⟩⟩,r⟩,h.2⟩,λ | .inl h=>h▸⟨(mF.1 (j (mG.2 ⟨x,c,rfl⟩))).1,by{rw[(d x c).2];exact m0 x},by{rw[(d x c).2,mS];exact λ hc=>a hc.symm}⟩ | .inr h=>⟨h.1.1.1,h.2⟩⟩};have H:(⟨b x,0⟩:U0)∉(residualUnits n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1):=λ hc=>(mD.1 (mF.1 hc).1).2 (mG.2 ⟨x,c,rfl⟩);rw[K,J,Finset.singleton_union,Finset.card_insert_of_notMem H];omega
lemma vw(c:q0 n D){x y:Fin n}(a:x≠y){w:Nat}(d:x∈fM n D w/\y∈fM n D w):∃j s,j<(tD D)/\gZ D j=p55/\x∈fM n D (n+j)/\y∈fM n D (n+j)/\x∈fM n D (fC D (j,s))/\y∉fM n D (fC D (j,s))/\y∈fM n D (fC D (j,!s))/\x∉fM n D (fC D (j,!s)):=by classical have l:∃u,x∈fM n D u/\y∈fM n D u:=⟨w,d⟩;obtain⟨m,p⟩:=p24 l;have i:∀u<p22 l,¬(x∈fM n D u/\y∈fM n D u):=λ _ J=>p23 l J;generalize p22 l=f at m p i;have L:=wx m;have Q:n<=f:=by{by_contra hc;have K:fM n D f={⟨f,by omega⟩}:=wc D ⟨f,by omega⟩;rw[K,mS] at m p;exact a (m.trans p.symm)};obtain⟨j,rfl⟩:∃j,f=n+j:=⟨f-n,by omega⟩;have H:j<(tD D):=by{omega};obtain⟨P,M,-⟩:=c j H;have q:=i _ P;have z:=i _ M;cases ht:gZ D j;{have h1':=m;have h2':=p;rw[yj c H ht,mN] at h1' h2';refine⟨j,?_⟩;rcases h1' with v|r;{have h:=λ hc=>q ⟨v,hc⟩;have g:=h2'.resolve_left h;exact⟨p55,H,ht,m,p,v,h,g,λ hc=>z ⟨hc,g⟩⟩};{have g:=λ hc=>z ⟨r,hc⟩;have h:=h2'.resolve_right g;exact⟨p63,H,ht,m,p,r,g,h,λ hc=>q ⟨hc,h⟩⟩}};{rw[qm c H ht,mI] at m p;exact absurd ⟨m.1,p.1⟩ q}
section
variable (K:w6 G)(H:fV n D)(C:gK n G D)(b:tY n)(P:gN n D b)
include K H C b P
lemma v4{x c z:Fin n}(a:x≠c)(m:x∈fX n D)(d:∀u∈residualUnits n D b,x∈fM n D u.1->c∈fM n D u.1){w:Nat}(p:x∈fM n D w/\c∈fM n D w)(j:G x z)(g:¬G c z):q6 D (q4 n D x c)=1/\w5 n D (q4 n D x c)=∅/\(qc n D (q4 n D x c)).card=2/\∃e∈qc n D (q4 n D x c),gZ D e.1=p55/\c∈fM n D (n+e.1):=by have hS:=H.1;have r:q6 D (q4 n D x c)=1:=by{rw[vp hS b P a m,gI.2 (λ u y hc=>hc.2 (d u y hc.1)),Finset.card_empty]};have h4:=va H x c a (qn K C▸nE x);rw[r] at h4;obtain⟨U,R,h3,Z,Y,Q,B,A,-,-⟩:=vw hS a p;have M:(U,R)∈qc n D (q4 n D x c):=y5.2 ⟨h3,⟨B,A⟩,λ hc=>hc.2 Q⟩;obtain⟨j2,s2,h1,-,X,N,h6⟩:=vc K hS C {c,z} (λ u y v J=>by{simp only[p43,mS] at y J;rcases y with rfl|rfl<;>rcases J with rfl|rfl;{exact K.2.1 _};{exact g};{exact λ hc=>g (K.1 _ _ hc)};{exact K.2.1 _}}) x ⟨z,by simp,j⟩;have h5:(j2,s2)∈qc n D (q4 n D x c):=y5.2 ⟨h1,⟨X,λ hc=>p36.1 h6 hc (by simp)⟩,λ hc=>N hc.1⟩;have:=p46.2 ⟨_,M,_,h5,λ L=>N ((Prod.mk.inj L).1▸Y)⟩;exact⟨r,g8.1 (by omega),by omega,(U,R),M,Z,Q⟩
lemma bb{x c:Fin n}(a:x≠c)(i:x∈fX n D)(d:∀u∈residualUnits n D b,x∈fM n D u.1->c∈fM n D u.1){w:Nat}(j:x∈fM n D w/\c∈fM n D w):∃e0,∀e∈fD n D x,e≠e0->c∈fM n D (fC D e):=by classical obtain⟨z,p,J⟩:=K.2.2.1 x c a;obtain⟨-,-,X,Q,y,q,-⟩:=v4 K H C b P a i d j p J;obtain⟨e0,B⟩:=p29.1 (show ((qc n D (q4 n D x c)).erase Q).card=1 by rw[Finset.card_erase_of_mem y,X]);refine⟨e0,λ e A r=>by_contra λ L=>?_⟩;obtain⟨Y,U,R⟩:=sM.1 A;exact r (mS.1 (B▸Finset.mem_erase.2 ⟨λ v=>Bool.false_ne_true (q▸v▸sA H.1 A),y5.2 ⟨Y,⟨U,L⟩,λ hc=>R hc.1⟩⟩))
end
end
end
end DagTools
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset (card_le_univ nodup_toList univ)
open List (Nodup)
open DagTools
abbrev V:=Fin 10
abbrev EdgeIdx:=Fin 14
section
open DagTools.A0
abbrev qO:=tJ
abbrev Slot:=qO
def k7:List (Nat×Nat):= choose ([(0,3),(0,7),(1,4),(1,9),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]) ([(0,8),(0,9),(1,4),(1,9),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]) ([(0,8),(0,9),(1,3),(1,7),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]) ([(0,8),(0,9),(1,3),(1,7),(2,4),(2,9),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)])
def gJ(x:Fin 10->Bool):Prop:=∃u v:Fin 10,(u.1,v.1)∈k7/\x u=p63/\x v=p63
def fL(C:Circuit):Prop:=∀x:Fin 10->Bool,C.eval (oF x)=p63↔gJ x
def neigh(v:V):Nat:= choose ([136,528,96,641,386,580,292,281,208,42].getD v.1 0) ([768,528,96,640,386,580,292,280,209,43].getD v.1 0) ([768,136,96,642,384,580,292,282,209,41].getD v.1 0) ([768,136,528,642,388,576,288,282,209,45].getD v.1 0)
abbrev adj(u v:V):Prop:=(neigh u).testBit v.1=p63
end
namespace A1
abbrev EI:=EdgeIdx
abbrev SL:=fV 10
abbrev PB:=gN 10
abbrev SC:=gK 10 adj
end A1
section
open DagTools.A0 DagTools.A0r DagTools.A0b A1
def ep0 (e:EI):V:=Fin.ofNat 10 (k7.getD e.val (0,0)).1
def ep1 (e:EI):V:=Fin.ofNat 10 (k7.getD e.val (0,0)).2
def endpoint (s:Bool)(e:EI):V:=if s then ep1 e else ep0 e
def sflip(s:Bool)(p:qO):qO:=(p.1,xor s p.2)
@[simp] lemma sflip_false(p:qO):sflip p55 p=p:=by rcases p with ⟨g,b⟩;simp[sflip]
@[simp] lemma sflip_true(p:qO):sflip p63 p=sem_bar p:=by rcases p with ⟨g,b⟩;cases b<;>rfl
lemma sflip_not(s:Bool)(p:qO):sflip (!s) p=sem_bar (sflip s p):=by rcases p with ⟨g,b⟩;cases s<;>cases b<;>rfl
lemma sflip_inj(s:Bool){p q:qO}(h:sflip s p=sflip s q):p=q:=by rcases p with ⟨g,c⟩;rcases q with ⟨d,a⟩;cases s<;>cases c<;>cases a<;>simp[sflip] at h ⊢<;>exact h
def js(u v:V):List EI->EI×Bool
 | []=>(0,p55)
 | e::rest=> if ep0 e==u&&ep1 e==v then (e,p55) else if ep1 e==u&&ep0 e==v then (e,p63) else js u v rest
def fW(u v:V):EI×Bool:=js u v (lR 14)
abbrev edgeOfPair:=fW
lemma wt(u v:V)(h:adj u v):endpoint (fW u v).2 (fW u v).1=u/\endpoint (!(fW u v).2) (fW u v).1=v:=by revert u v h;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma graph_ok:w6 adj:=by unfold w6;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
namespace A1b
abbrev G0:=graph_ok
end A1b
open A1b
lemma ja:∀u v:V,adj u v↔(u.1,v.1)∈k7\/(v.1,u.1)∈k7:=by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma xk(e:EI):adj (ep0 e) (ep1 e):=by revert e;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma xm(x:V->Bool):gJ x↔yi adj x:=by constructor;{rintro⟨u,v,e,d,c⟩;exact⟨u,v,(ja u v).2 (o1 e),d,c⟩};{rintro⟨u,v,a,d,c⟩;rcases (ja u v).1 a with e|e;{exact⟨u,v,e,d,c⟩};{exact⟨v,u,e,c,d⟩}}
lemma xu:¬gJ (λ _=>p55):=by rintro⟨_,_,_,h,_⟩;contradiction
lemma k8(i:V):¬gJ (q9 i):=λ h=>wd G0 i ((xm _).1 h)
lemma normalized(C:Circuit)(c:Monotone2 C)(a:fL C):∃D:qD,SL D/\(tD D)<=C.size/\SC D:=by obtain⟨D,l,le,m⟩:=zy (n:=10) C c (by{intro b;cases b;{refine⟨λ _=>p63,?_⟩;rw[Ne,p59];exact (a _).2 ⟨7,8,by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide,rfl,rfl⟩};{exact⟨λ _=>p55,λ h=>xu ((a _).1 h)⟩}}) (by{intro i;exact⟨q9 i,λ h=>k8 i ((a _).1 (by rw[h];simp[q9]))⟩}) (by{intro i;obtain⟨j,g,_⟩:=G0.2.2.2 i i;refine⟨q9 j,q1 i j,?_,?_⟩;{intro k d;simp[q1,q9,d]};{intro h;exact k8 j ((a _).1 (h.trans ((a _).2 ((xm _).2 (yv g)))))}});exact⟨D,l,le,λ x=>by rw[m,a];exact xm x⟩
def mask (m:Nat):Finset V:=univ.filter (λ v=>m.testBit v.val)
abbrev independent(T:tF V):Prop:=∀a∈T,∀b∈T,¬adj a b
def zw(a:EP V):Prop:=∀i j,adj (a i) (a j)↔adj i j
def w4(a:List Nat)(v:V):V:=Fin.ofNat 10 (a.getD v.1 0)
def gA:EP V:=Equiv.refl V
def specialPerm:EP V:=⟨w4 [0,3,2,1,7,5,6,4,8,9],w4 [0,3,2,1,7,5,6,4,8,9],by decide +kernel,by decide +kernel⟩
def gB : EP V := if sctx.default.val = 1 then specialPerm else gA
def autPerm(a:Fin 2):EP V:=match a.1 with|0=>gA|_=>gB
lemma bd:zw gA:=by intro i j;rfl
lemma be:zw gB:=by unfold zw;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma auto_autPerm(a:Fin 2):zw (autPerm a):=by fin_cases a;{exact bd};{exact be}
lemma rename{D:qD}(h:SL D)(d:SC D)(c:EP V)(a:zw c):SC (relabel c D):=by intro x;rw[xa c h.1 h.2.2,d];constructor;{rintro⟨u,v,g,j,i⟩;exact⟨c u,c v,(a _ _).2 g,j,i⟩};{rintro⟨u,v,g,j,i⟩;refine⟨c.symm u,c.symm v,(a _ _).1 (by simpa using g),by simpa using j,by simpa using i⟩}
lemma yn(a:EP V)(D:qD)(c:D≠[]){w:Nat}:gL a w∈inner 10 (relabel a D)↔w∈inner 10 D:=by have g:0<(tD D):=lP c;simp only[inner,mR,rL];by_cases d:w<10;{rw[yh a d];have:=(a ⟨w,d⟩).2;omega};{rw[qt a (by omega)]}
def gn(a:EP V)(b:V->Nat)(v:V):Nat:=gL a (b (a.symm v))
abbrev relabelBranch:=gn
lemma relabel_pureBranch(a:EP V){D:qD}(c:q0 10 D){b:V->Nat}(d:PB D b):PB (relabel a D) (gn a b):=by intro v h;rw[ym a c] at h;obtain⟨u,i,rfl⟩:=mG.1 h;have g:=d u i;simp only[gn,Equiv.symm_apply_apply];refine⟨by rw[wa];exact g.1,?_⟩;rw[rS a c,g.2,Finset.image_singleton]
lemma relabel_residualUnits_mem(a:EP V){D:qD}(h:SL D)(b:V->Nat)(u:U0):(⟨gL a u.1,u.2⟩:U0)∈residualUnits 10 (relabel a D) (gn a b)↔u∈residualUnits 10 D b:=by rcases u with ⟨w,i⟩;simp only[residualUnits,mD,ww,units,mF,p44,mR,qh,mG,ym a h.1,yn a D h.2.2,wa,rS a h.1,p39,Sigma.mk.inj_iff,heq_eq_eq];exact⟨λ⟨⟨⟨l,hr⟩,g⟩,d⟩=>⟨⟨⟨l,hr⟩,g⟩,λ⟨v,j,c⟩=>d ⟨a v,⟨v,j,rfl⟩,by simpa[gn] using ⟨congrArg (gL a) c.1,c.2⟩⟩⟩,λ⟨⟨⟨l,hr⟩,g⟩,d⟩=>⟨⟨⟨l,hr⟩,g⟩,λ⟨_,⟨v,j,rfl⟩,c⟩=>d ⟨v,j,by{simp only[gn,Equiv.symm_apply_apply] at c;exact⟨(gq a).1 c.1,c.2⟩}⟩⟩⟩
def gP(D:qD)(a:EI->qO):Prop:=∀s e,sflip s (a e)∈fD 10 D (endpoint s e)/\endpoint (!s) e∉fM 10 D (fC D (sflip s (a e)))
abbrev GoodEdge:=gP
lemma get_edges{D:qD}(c:q0 10 D)(a:SC D):∃edge:EI->qO,gP D edge:=by classical have j:∀e:EI,∃p:qO,p∈fD 10 D (ep0 e)/\sem_bar p∈fD 10 D (ep1 e)/\ep1 e∉fM 10 D (fC D p)/\ep0 e∉fM 10 D (fC D (sem_bar p)):=by{intro e;obtain⟨p,i,h,g,d,_⟩:=z5 G0 c a (xk e);exact⟨p,i,h,g,d⟩};choose edge hedge using j;refine⟨edge,λ s e=>?_⟩;cases s;{simpa[endpoint,sflip_false] using ⟨(hedge e).1,(hedge e).2.2.1⟩};{simpa[endpoint,sflip_true] using ⟨(hedge e).2.1,(hedge e).2.2.2⟩}
def relabelEdge(c:EP V)(a:EI->qO)(e:EI):qO:=let p:=fW (c.symm (ep0 e)) (c.symm (ep1 e));sflip p.2 (a p.1)
lemma relabelEdge_fst(c:EP V)(a:EI->qO)(e:EI):(relabelEdge c a e).1=(a (fW (c.symm (ep0 e)) (c.symm (ep1 e))).1).1:=rfl
lemma surplus_bound{D:qD}(h:SL D)(a:(tD D)<=18)(b:V->Nat)(c:PB D b):(residualUnits 10 D b).card+Bzero 10 D+1<=(ineligSet 10 D).card:=by have j:=vj h;have i:=jz 10 D;have g:=vu 10 D;have d:=kf h.1 b c;omega
lemma inelig_indep{D:qD}(h:SL D)(c:SC D):independent (ineligSet 10 D):=by intro a l b j i;rcases j5 G0 h c i with g|d;{exact (sE.1 l) g};{exact (sE.1 j) d}
def orbitMasks:List Nat:= choose ([1,2,4,8,16,32,64,128,256,512,3,5,6,10,12,17,20,24,33,34,40,48,65,66,72,80,130,132,160,192,257,258,260,264,288,513,516,528,576,640,768,7,14,21,28,35,42,49,56,67,74,81,88,134,162,194,259,261,262,266,268,289,290,296,517,529,532,577,592,644,704,769,772,263,270,291,298,533,593,773]) ([1,2,4,16,32,64,256,512,3,5,17,33,65,6,10,34,66,130,258,20,260,516,48,80,528,288,576,768,7,11,35,67,131,21,49,81,14,134,262,42,74,266,162,290,194,532,772,592,15,135,43,75,163,195,270,298]) ([1,2,4,8,16,32,64,128,256,512,3,5,6,9,12,17,18,20,24,33,34,40,48,65,66,72,80,129,132,160,192,258,260,264,288,514,516,528,576,640,768,7,13,19,21,22,25,28,35,41,49,50,56,67,73,81,82,88,133,161,193,262,268,290,296,518,530,532,578,592,644,704,770,772,23,29,51,57,83,89,534,594,774]) ([1,2,4,8,16,32,64,128,256,512,3,5,6,9,12,17,18,24,33,34,36,40,48,65,66,68,72,80,129,132,160,192,258,260,264,288,514,528,576,640,768,7,13,19,25,35,37,38,41,44,49,50,56,67,69,70,73,76,81,82,88,133,161,164,193,196,262,268,290,292,296,530,578,592,704,770,39,45,51,57,71,77,83,89,165,197,294,300,594])
def maskImage(a:Fin 2)(m:Nat):Nat:=(lR 10).foldl (λ c v=>if m.testBit v.1 then c|||(1<<<(autPerm a v).1) else c) 0
lemma za(n k:Nat):(1<<<n).testBit k=decide (n=k):=by rw[p26,Nat.testBit_two_pow]
lemma k9(a:Fin 2)(m:Nat)(L:List V)(c:Nat)(k:Nat):(L.foldl (λ s v=>if m.testBit v.1 then s|||(1<<<(autPerm a v).1) else s) c).testBit k=(c.testBit k||L.any (λ v=>m.testBit v.1&&decide ((autPerm a v).1=k))):=by induction L generalizing c with|nil=>{simp}|cons v d ih=>{simp only[lO,p1,ih];by_cases g:m.testBit v.1=p63;{simp only[g,ite_true,p64,p27,za,p62]};{simp only[g,bF,ite_false,p56,p57]}}
lemma mask_maskImage(a:Fin 2)(m:Fin 1024):mask (maskImage a m.1)=(mask m.1).image (autPerm a):=by ext u;simp only[mask,maskImage,mF,mU,true_and,mG,k9,p28,p57,p2,hC,bA,dT];constructor;{rintro⟨v,d,c⟩;exact⟨v,d,Fin.ext c⟩};{rintro⟨v,d,rfl⟩;exact⟨v,d,rfl⟩}
def jc(m:Nat):Bool:=k7.all (λ e=>!(m.testBit e.1&&m.testBit e.2))
def zc(m:Nat):Bool:=m==0||!jc m||(lR 2).any (λ a=>orbitMasks.elem (maskImage a m))
def wu(lo:Nat):Nat->Bool
 | 0=>p63
 | n+1=>zc lo&&wu (lo+1) n
lemma v5:(p20 16).all (λ b=>wu (b*64) 64)=p63:=by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma jd(a n m:Nat)(h:wu a n=p63)(c:a<=m)(d:m<a+n):zc m=p63:=by induction n generalizing a with|zero=>{omega}|succ n ih=>{simp only[wu,bA] at h;by_cases g:m=a;{subst g;exact h.1};{exact ih (a+1) h.2 (by omega) (by omega)}}
lemma je{m:Nat}(a:independent (mask m)):jc m=p63:=by unfold jc;rw[p0];intro e d;have c:e.1<10/\e.2<10:=of_decide_eq_true (p0.1 (show k7.all (λ p=>decide (p.1<10/\p.2<10))=p63 by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel) e d);cases h:m.testBit e.1<;>cases g:m.testBit e.2;rfl;rfl;rfl;exact absurd ((ja ⟨e.1,c.1⟩ ⟨e.2,c.2⟩).2 (.inl d)) (a ⟨e.1,c.1⟩ (mF.2 ⟨mU _,h⟩) ⟨e.2,c.2⟩ (mF.2 ⟨mU _,g⟩))
lemma orbit_dispatch(m:Fin 1024)(d:m.1≠0)(c:independent (mask m.1)):∃a:Fin 2,maskImage a m.1∈orbitMasks:=by have j:=jd ((m.1/64)*64) 64 m.1 (p0.1 v5 (m.1/64) (p17.2 (by omega))) (by omega) (by omega);simp only[zc,je c,p61,Bool.or_false,bO,beq_iff_eq,p2,hC,true_and,List.elem_eq_mem,dT] at j;exact j.resolve_left d
lemma kj(S:tF V)(L:List V)(a:Nat)(k:Nat):(L.foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) a).testBit k=(a.testBit k||L.any (λ v=>decide (v∈S)&&decide (v.1=k))):=by induction L generalizing a with|nil=>{simp}|cons v c ih=>{simp only[lO,p1,ih];by_cases d:v∈S;{simp only[d,ite_true,decide_true,p64,p27,za,p62]};{simp only[d,ite_false,decide_false,p56,p57]}}
lemma kx(S:tF V)(L:List V)(c:Nat)(a:c<2^10):L.foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) c<2^10:=by induction L generalizing c with|nil=>{exact a}|cons v d ih=>{simp only[lO];by_cases g:v∈S;{simp only[g,ite_true];apply ih;apply Nat.or_lt_two_pow a;rw[p26];exact Nat.pow_lt_pow_right (by omega) v.2};{simp only[g,ite_false];exact ih c a}}
lemma repr_finset(S:tF V):∃m:Fin 1024,mask m.1=S:=by let n:Nat:=(lR 10).foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) 0;refine⟨⟨n,kx S (lR 10) 0 (by omega)⟩,?_⟩;ext v;simp only[mask,mF,mU,true_and,n,kj,p28,p57,p2,hC,bA,dT];exact⟨λ⟨u,d,a⟩=>Fin.ext a▸d,λ c=>⟨v,c,rfl⟩⟩
def fF(D:qD)(x:V):Nat:=(fD 10 D x).card
def cap(k I:Nat)(x:V):Nat:=if I.testBit x.1 then 1 else 2+k
def gQ(D:qD)(x:V)(j:Nat):Prop:=j<fF D x
abbrev SLive:=gQ
def Together(D:qD)(x c:V):Prop:=∃w,x∈fM 10 D w/\c∈fM 10 D w
def ineligNbrs(I:Nat)(x:V):List V:=(lR 10).filter (λ y=>(neigh x).testBit y.1&&I.testBit y.1)
def eligNbrs(I:Nat)(x:V):List V:=(lR 10).filter (λ y=>(neigh x).testBit y.1&&!I.testBit y.1)
def pinTarget(a:EI->qO)(x y:V):qO:=let p:=fW x y;sflip p.2 (a p.1)
def pinSlots(I:Nat)(a:EI->qO)(x:V):List qO:=let c:=ineligNbrs I x;let d:=eligNbrs I x;c.map (pinTarget a x)++match d with|[]=>[]|y::_=>[pinTarget a x y]
def yk(D:qD)(w:Nat):Nat:=∑ v∈fM 10 D w,2^v.1
def zl(D:qD):Option U0->Nat
 | none=>0
 | some u=>yk D u.1
def GoodLayout(D:qD)(k I:Nat)(d:V->Nat->qO)(g:EI->qO)(c:V->Nat)(a:Fin k->Option U0):Prop:=PB D c/\(∀u∈residualUnits 10 D c,∃t:Fin k,a t=some u)/\(∀t u,a t=some u->u∈residualUnits 10 D c)/\(∀i h u,a i=some u->a h=some u->i=h)/\(∀i h:Fin k,i.1<h.1->zl D (a i)<=zl D (a h))/\(∀x,fF D x<=cap k I x)/\(∀x j,d x j∈fD 10 D x)/\(∀x m l,m<fF D x->l<fF D x->d x m=d x l->m=l)/\(∀x e,e∈fD 10 D x->∃j<fF D x,d x j=e)/\gP D g/\(∀x:V,¬I.testBit x.1->∀r,(hr:r<(pinSlots I g x).length)->r<fF D x/\d x r=(pinSlots I g x)[r])
end
namespace A2
abbrev G1:=GoodLayout
abbrev L5{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.1
abbrev L6{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.1
abbrev L7{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.1
abbrev L8{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.2.1
abbrev L9{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.2.2.1
end A2
section
open DagTools.A0 DagTools.A0r DagTools.A0b A1 A1b A2
lemma pinTarget_mem_W{D:qD}{a:EI->qO}(c:gP D a){x y:V}(i:adj x y):pinTarget a x y∈fD 10 D x/\sem_bar (pinTarget a x y)∈fD 10 D y:=by have d:=wt x y i;unfold pinTarget;have h:=(c (fW x y).2 (fW x y).1).1;have g:=(c (!(fW x y).2) (fW x y).1).1;rw[d.1] at h;rw[d.2,sflip_not] at g;exact⟨h,g⟩
lemma z6{D:qD}(h:SL D)(g:SC D){I:Nat}(c:mask I=ineligSet 10 D){a:EI->qO}(d:gP D a)(x:V):(pinSlots I a x).Nodup/\∀p∈pinSlots I a x,p∈fD 10 D x:=by have i:∀y∈ineligNbrs I x,adj x y/\y∈ineligSet 10 D:=λ y v=>by{simp only[ineligNbrs,p15,hC,true_and,bA] at v;exact⟨v.1,c▸mF.2 ⟨mU _,v.2⟩⟩};have j:∀y∈eligNbrs I x,adj x y/\y∉ineligSet 10 D:=λ y v=>by{simp only[eligNbrs,p15,hC,true_and,bA,Bool.not_eq_true'] at v;exact⟨v.1,by{rw[<-c,mask,mF];simp[v.2]}⟩};have u:∀y∈ineligNbrs I x,fM 10 D (fC D (sem_bar (pinTarget a x y)))={y}:=λ y v=>sP G0 h.1 g (i y v).2 (sM.1 (pinTarget_mem_W d (i y v).1).2).2.1;have H:((ineligNbrs I x).map (pinTarget a x)).Nodup:=Nodup.map_on (λ M h0 L Z U=>p48 (((u M h0).symm.trans (U.symm▸u L Z)))) ((List.nodup_finRange 10).filter _);constructor;{unfold pinSlots;cases r:eligNbrs I x with|nil=>{simpa using H}|cons y _=>{refine p19.2 ⟨H,List.nodup_singleton _,λ p h3 q hq U=>?_⟩;simp only[lS] at hq;subst hq U;obtain⟨z,hz,Q⟩:=p16.1 h3;have ⟨hxy,hyn⟩:=j y (r▸p14);have l:=(sM.1 (pinTarget_mem_W d hxy).2).2.1;rw[<-Q,u z hz,mS] at l;exact hyn (l▸(i z hz).2)}};{intro p m;unfold pinSlots at m;rcases g6.1 m with Y|X;{obtain⟨y,v,rfl⟩:=p16.1 Y;exact (pinTarget_mem_W d (i y v).1).1};{cases r:eligNbrs I x with|nil=>{simp[r] at X}|cons y _=>{simp only[r,lS] at X;subst X;exact (pinTarget_mem_W d (j y (r▸p14)).1).1}}}
lemma jn{D:qD}(h:SL D)(d:SC D){I:Nat}(c:mask I=ineligSet 10 D){a:EI->qO}(g:gP D a)(x:V):(pinSlots I a x).length<=fF D x:=by obtain⟨j,i⟩:=z6 h d c g x;rw[<-p21 j];exact p34 (λ p l=>i p (p18.1 l))
def b4(I:Nat)(x:V):Nat:=(ineligNbrs I x).length+if (eligNbrs I x).isEmpty then 0 else 1
lemma vx(I:Nat)(a:EI->qO)(x:V):(pinSlots I a x).length=b4 I x:=by unfold pinSlots b4;cases eligNbrs I x<;>simp
section
variable {D:qD}(H:SL D)(S:SC D){k I:Nat}(M:mask I=ineligSet 10 D){b:V->Nat}(P:PB D b)(K:(residualUnits 10 D b).card<=k)
include D H S k I M b P K
lemma jf(x:V):fF D x<=cap k I x:=by unfold cap fF;by_cases l:I.testBit x.1=p63;{simp only[l,ite_true];have j:x∈ineligSet 10 D:=M▸mF.2 ⟨mU _,l⟩;obtain⟨p,_,_,_,_,_,m,_⟩:=qe G0 H S j;change fD 10 D x={p} at m;rw[m,fw]};{simp[l];have i:=p34 (fI:({x}:tF V)∩fX 10 D⊆{x});have:=hO (residualUnits 10 D b) (λ u=>x∈fM 10 D u.1);have:=j7 G0 H S b P x;simp only[fw] at i;omega}
lemma pin_kill(x:V)(d:I.testBit x.1=p55)(g:2+k<b4 I x):False:=by obtain⟨l,m⟩:=get_edges H.1 S;have q:=jn H S M m x;rw[vx] at q;have p:=jf H S M P K x;simp only[cap,d,bF,ite_false] at p;omega
lemma construct_layout_from{d:EI->qO}(l:gP D d):∃(wire:V->Nat->qO) (order:Fin k->Option U0),G1 D k I wire d b order:=by classical let R:=(residualUnits 10 D b).toList;let A:=R.mergeSort (λ u v=>decide (yk D u.1<=yk D v.1));have U:A.Perm R:=List.mergeSort_perm R _;have h7:A.length=(residualUnits 10 D b).card:=U.length_eq.trans (Finset.length_toList _);have h4:A.Nodup:=U.nodup_iff.2 (nodup_toList _);have hf:A.Pairwise (λ u v=>yk D u.1<=yk D v.1):=(List.pairwise_mergeSort (le:=λ u v:U0=>decide (yk D u.1<=yk D v.1)) (λ _ _ _ h1 h2=>decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))) (λ _ _=>by simp[Nat.le_total]) R).imp of_decide_eq_true;let C:List (Option U0):=List.replicate (k-A.length) none++A.map some;have X:C.length=k:=by{simp[C,h7];omega};let order:Fin k->Option U0:=λ t=>C[t.1]'(X.symm▸t.2);let L (x:V):List qO:=if I.testBit x.1 then [] else pinSlots I d x;have Z (x:V):(L x).Nodup:=by{unfold L;split;exact .nil;exact (z6 H S M l x).1};have Y (x:V):∀p∈L x,p∈fD 10 D x:=by{unfold L;split;simp;exact (z6 H S M l x).2};let J (x:V):List qO:=L x++((fD 10 D x) \ (L x).toFinset).toList;have h3 (x:V):(J x).Nodup:=p19.2 ⟨Z x,nodup_toList _,λ p hp q hq h5=>by{subst h5;exact (mD.1 (p45.1 hq)).2 (p18.2 hp)}⟩;have N (x:V) (p:qO):p∈J x↔p∈fD 10 D x:=by{simp only[J,g6,p45,mD,p18];exact⟨λ | .inl h1=>Y x p h1 | .inr h2=>h2.1,λ h1=>if hp:p∈L x then .inl hp else .inr ⟨h1,hp⟩⟩};have B (x:V):(J x).length=fF D x:=by{rw[<-p21 (h3 x)];congr 1;ext p;simp[N]};let wire (x:V) (j:Nat):qO:=if hj:j<(J x).length then (J x)[j] else (J x)[0]'(by{rw[B];obtain⟨y,xy,_⟩:=G0.2.2.2 x x;obtain⟨p,hp,_⟩:=z5 G0 H.1 S xy;exact fz.2 ⟨p,hp⟩});refine⟨wire,order,P,?_,?_,?_,?_,jf H S M P K,?_,?_,?_,l,?_⟩;{intro u hu;obtain⟨ht,f1,rfl⟩:=p7 (U.mem_iff.2 (p45.2 hu));exact⟨⟨k-A.length+ht,by omega⟩,by{simp only[order,C];rw[hH (by simp)];simp}⟩};{intro t u hw;have Q:some u∈C:=hw▸hL _;simp only[C,g6,List.mem_replicate,p16] at Q;rcases Q with ⟨_,hh⟩|⟨v,hv,h5⟩;cases hh;cases h5;exact p45.1 (U.mem_iff.1 hv)};{intro t1 t2 u h1 h2;have f2:∀t:Fin k,order t=some u->k-A.length<=t.1:=λ t ht=>by{by_contra c;simp only[order,C] at ht;rw[hG (by{simp;omega}),List.getElem_replicate] at ht;cases ht};have:=f2 t1 h1;have:=f2 t2 h2;simp only[order,C] at h1 h2;rw[hH (by{simp;omega})] at h1 h2;simp only[hK,List.getElem_map,hI] at h1 h2;have:=(Nodup.getElem_inj_iff h4).1 (h1.trans h2.symm);exact Fin.ext (by omega)};{intro t1 t2 c;have hg:C.Pairwise (λ a b=>zl D a<=zl D b):=by{rw[List.pairwise_append];refine⟨List.pairwise_replicate.2 (.inr (Nat.le_refl 0)),List.pairwise_map.2 hf,?_⟩;intro a ha _ _;rw[List.eq_of_mem_replicate ha];exact nZ _};exact List.pairwise_iff_getElem.1 hg t1.1 t2.1 (X.symm▸t1.2) (X.symm▸t2.2) c};{intro x j;unfold wire;split<;>exact (N x _).1 (hL _)};{intro x j1 j2 hm hl h5;rw[<-B x] at hm hl;simp only[wire,hm,hl,hD] at h5;exact (Nodup.getElem_inj_iff (h3 x)).1 h5};{intro x e he;obtain⟨j,hj,rfl⟩:=p7 ((N x e).2 he);exact⟨j,B x▸hj,by simp[wire,hj]⟩};{intro x hy r hr;have hd:L x=pinSlots I d x:=by{simp[L,hy]};have c:r<(J x).length:=by{simp only[J,lA,hd];omega};exact⟨B x▸c,by{simp only[wire,c,hD,J];rw[hG (hd▸hr)];simp[hd]}⟩}
end
def resAt(D:qD){k:Nat}(a:Fin k->Option U0)(t:Nat)(x:V):Prop:=∃c:t<k,match a ⟨t,c⟩ with|none=>False|some u=>x∈fM 10 D u.1
def gR(D:qD)(x:V):Prop:=1<=(w5 10 D (q2 10 D {x})).card
abbrev has_merge:=gR
def opp(D:qD)(a:V->Nat->qO)(x:V)(j:Nat)(y:V):Prop:=gQ D x j/\y∈fM 10 D (fC D (sem_bar (a x j)))
def lab(D:qD)(a:V->Nat->qO)(x:V)(j:Nat)(y:V):Prop:=gQ D x j/\y∈fM 10 D (fC D (a x j))
def rsub(D:qD){k:Nat}(c:V->Nat->qO)(a:Fin k->Option U0)(t:Nat)(x:V)(j:Nat):Prop:=gQ D x j/\∀y:V,resAt D a t y->lab D c x j y
def ra(D:qD)(a:V->Nat->qO)(c:EI->qO)(s:Bool)(e:EI)(x:V)(j:Nat):Prop:=gQ D x j/\a x j=sflip s (c e)
def gT(D:qD)(a:V->Nat->qO)(c:EI->qO)(x:V)(j:Nat):Prop:=gQ D x j/\∀(e:EI) (s:Bool),a x j≠sflip s (c e)
abbrev free_slot:=gT
def gU(D:qD)(a:V->Nat->qO)(x:V)(j:Nat):Prop:=gQ D x j/\fM 10 D (fC D (sem_bar (a x j)))=∅
abbrev empty_opp:=gU
def after(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=gQ D x j/\(c e).1<(a x j).1
def afree(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=after D a c e x j/\gT D a c x j
def aempty(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=after D a c e x j/\gU D a x j
lemma hmInelig{D:qD}(h:SL D)(c:SC D){x:V}(a:x∈ineligSet 10 D):¬gR D x:=by obtain⟨_,_,_,_,_,_,_,d⟩:=qe G0 h c a;simp[gR,d]
lemma ka{D:qD}{a:V->Nat->qO}{c:EI->qO}(g:gP D c){x:V}{j:Nat}(d:gU D a x j):gT D a c x j:=by refine⟨d.1,λ e s i=>?_⟩;have l:=(g (!s) e).1;rw[sflip_not,<-i] at l;have h:=(sM.1 l).2.1;rw[d.2] at h;exact nE _ h
lemma commonInelig{D:qD}(g:q0 10 D)(d:SC D){x y:V}(c:x∈ineligSet 10 D)(a:x≠y):¬Together D x y:=by rintro⟨w,hxw,hyw⟩;have h:=sP G0 g d c hxw;rw[h,mS] at hyw;exact a hyw.symm
section
variable {D:qD} {k I:Nat} {W:V->Nat->qO} {E:EI->qO} {F:V->Nat} {O:Fin k->Option U0}
lemma commonExit_of(h:SL D)(d:SC D)(c:G1 D k I W E F O){x y:V}(a:Together D x y):(∃j<cap k I x,lab D W x j y)\/(∃l<cap k I y,lab D W y l x):=by obtain⟨w0,v,U⟩:=a;let S:=(g5 (10+(tD D))).filter (λ w=>x∈fM 10 D w/\y∈fM 10 D w);have M:S.Nonempty:=⟨w0,mF.2 ⟨mR.2 (wx v),v,U⟩⟩;set w:=S.max' M;have ⟨H,hxw,hyw⟩:=mF.1 (p42 S M);have:=mR.1 H;have z:w+1<10+(tD D):=by{have p:w≠qb 10 D:=λ h0=>nE x (qn G0 d▸h0▸hxw);unfold qb at p;omega};obtain⟨g,hg⟩:=fz.1 (nT nO (h.2.1 w z));obtain⟨q,Q⟩:=mF.1 hg;have hg_lt':=mR.1 q;obtain⟨s,K⟩:=sX Q;have J:=K▸w7 h.1 hg_lt' s;have m:¬(x∈fM 10 D (10+g)/\y∈fM 10 D (10+g)):=λ r=>by{have:=p41 S (10+g) (mF.2 ⟨mR.2 (by omega),r⟩);omega};by_cases u:x∈fM 10 D (10+g);{obtain⟨l,i,X⟩:=L8 c y (g,s) (sM.2 ⟨hg_lt',K▸hyw,λ hy=>m ⟨u,hy⟩⟩);exact .inr ⟨l,lL i (L5 c y),i,X▸K▸hxw⟩};{obtain⟨j,i,Y⟩:=L8 c x (g,s) (sM.2 ⟨hg_lt',K▸hxw,u⟩);exact .inl ⟨j,lL i (L5 c x),i,Y▸K▸hyw⟩}
lemma labLive_of{x y:V}{j:Nat}(h:lab D W x j y):gQ D x j:=h.1
lemma selfLab_of(c:G1 D k I W E F O){x:V}{j:Nat}(a:gQ D x j):lab D W x j x:=⟨a,(sM.1 (L6 c x j)).2.1⟩
lemma labCommon_of(c:G1 D k I W E F O){x y:V}{j:Nat}(a:lab D W x j y):Together D x y:=⟨fC D (W x j),(sM.1 (L6 c x j)).2.1,a.2⟩
lemma live0_of(c:q0 10 D)(a:SC D)(x:V):gQ D x 0:=by obtain⟨y,d,_⟩:=G0.2.2.2 x x;obtain⟨p,g,_⟩:=z5 G0 c a d;exact fz.2 ⟨p,g⟩
lemma ineligNoRes_of(d:G1 D k I W E F O)(a:mask I=ineligSet 10 D){t:Nat}{x:V}(c:I.testBit x.1=p63):¬resAt D O t x:=by rintro⟨p,g⟩;cases j:O ⟨t,p⟩ with|none=>{rw[j] at g;exact g}|some u=>{rw[j] at g;have:=mR.1 (p44.1 (mF.1 (mD.1 (d.2.2.1 ⟨t,p⟩ u j)).1).1).2;exact (sE.1 (a▸mF.2 ⟨mU _,c⟩)) (zz.2 ⟨u.1,by omega,g⟩)}
lemma resCommon_of{t:Nat}{x y:V}(a:resAt D O t x)(c:resAt D O t y):Together D x y:=by obtain⟨g,a⟩:=a;obtain⟨_,c⟩:=c;cases d:O ⟨t,g⟩ with|none=>{rw[d] at a;exact a.elim}|some u=>{rw[d] at a c;exact⟨u.1,a,c⟩}
lemma adjCommon_of(h:SL D)(d:SC D){i a b:V}(c:i∈ineligSet 10 D)(j:adj i a)(g:adj i b):Together D a b:=by obtain⟨e,_,_,_,_,l,_,_⟩:=qe G0 h d c;exact⟨fC D (e.1,!e.2),l a j,l b g⟩
lemma ky(a:G1 D k I W E F O)(x:V):haveI:=cP (λ t:Fin k=>resAt D O t.1 x);((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card=((residualUnits 10 D F).filter (λ u=>x∈fM 10 D u.1)).card:=by classical let S:=(p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x);let T:=(residualUnits 10 D F).filter (λ u=>x∈fM 10 D u.1);have g:∀t∈S,∃u∈T,O t=some u:=λ t L=>by{obtain⟨_,c⟩:=(mF.1 L).2;cases p:O t with|none=>{rw[p] at c;exact c.elim}|some u=>{rw[p] at c;exact⟨u,mF.2 ⟨a.2.2.1 t u p,c⟩,rfl⟩}};have Y:=hN (λ t=>(O t).getD ⟨0,0⟩) (λ t L=>by{obtain⟨u,h,p⟩:=g t L;simpa[p] using h}) (λ R K Q J d=>by{obtain⟨v,_,m⟩:=g R K;obtain⟨P,_,l⟩:=g Q J;simp only[m,l,Option.getD_some] at d;exact a.2.2.2.1 R Q v m (d▸l)});have X:T.card<=S.card:=by{by_cases U:k=0;{subst U;have M:T=∅:=fE.2 (λ u h=>(a.2.1 u (mF.1 h).1).elim (λ t _=>t.elim0));simp[M]};choose f hf using a.2.1;refine hN (λ u=>if h:u∈residualUnits 10 D F then f u h else ⟨0,Nat.pos_of_ne_zero U⟩) (λ u h=>by{have ⟨j,y⟩:=mF.1 h;simp only[j,hD];exact mF.2 ⟨mU _,(f u j).2,by simpa[hf u j] using y⟩}) (λ v H P z d=>by{have r:=(mF.1 H).1;have q:=(mF.1 z).1;simp only[r,q,hD] at d;exact Option.some.inj ((hf v r).symm.trans (d▸hf P q))})};change S.card=T.card;omega
lemma sC{x:V}{d:Nat}{S:tF (Fin k)}[DecidablePred (λ t:Fin k=>resAt D O t.1 x)](i:S.card=k-d)(u:d+1<=((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card):∃t∈S,resAt D O t.1 x:=by by_contra l;push Not at l;let C:=(p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x);have m:(S∪C).card<=k:=by{simpa using card_le_univ (S∪C)};rw[fU (p36.2 λ t r p=>l t r (mF.1 p).2)] at m;omega
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O)
include H S G
lemma wo(x:V):haveI:=cP (λ t:Fin k=>resAt D O t.1 x);fF D x+(w5 10 D (q2 10 D {x})).card<=2+((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card:=by classical have i:=j7 G0 H S F G.1 x;have d:=p34 (fI:({x}:tF V)∩fX 10 D⊆{x});simp only[fw] at d;have g:=ky G x;change ((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card=_ at g;unfold fF;omega
lemma sizeCode_of(x:V)(d:Nat)(A:tF (Fin k))(i:A.card=k-d)(a:gQ D x (2+d)):∃t∈A,resAt D O t.1 x:=by classical have q:=wo H S G x;exact sC i (by{unfold gQ at a;change _<=2+_ at q;omega})
lemma hmTop_of(x:V)(a:gR D x):¬gQ D x (1+k):=by classical intro g;have i:=wo H S G x;let C:=(p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x);have:C.card<=k:=by{simpa using card_le_univ C};unfold gQ at g;unfold gR at a;change _<=2+C.card at i;omega
lemma hmCode_of(x:V)(d:Nat)(A:tF (Fin k))(j:A.card=k-d)(c:gR D x)(a:gQ D x (1+d)):∃t∈A,resAt D O t.1 x:=by classical have r:=wo H S G x;exact sC j (by{unfold gQ at a;unfold gR at c;change _<=2+_ at r;omega})
lemma riSlots_of(p:mask I=ineligSet 10 D){x c:V}(m:x≠c)(q:I.testBit x.1=p55){j l:Nat}(d:j<l)(a:gQ D x l)(g:Together D x c):lab D W x j c\/lab D W x l c\/∃t:Fin k,resAt D O t.1 x/\¬resAt D O t.1 c:=by by_contra P;push Not at P;obtain⟨J,A,K⟩:=P;have y:x∈fX 10 D:=by_contra λ Q=>by{have U:=sE.2 Q;rw[<-p,mask,mF] at U;simp[q] at U};obtain⟨w,hw⟩:=g;obtain⟨e0,X⟩:=bb G0 H S F G.1 m y (λ u hu Y=>by{obtain⟨t,ht⟩:=G.2.1 u hu;obtain⟨_,L⟩:=K t ⟨t.2,by simpa[ht] using Y⟩;simpa[ht] using L}) hw;have v:=lt_trans d a;have z:W x j≠W x l:=λ h1=>Nat.ne_of_lt d (L7 G x j l v a h1);by_cases R:W x j=e0;exact A ⟨a,X (W x l) (L6 G x l) (λ h2=>z (R.trans h2.symm))⟩;exact J ⟨v,X (W x j) (L6 G x j) R⟩
lemma expose_of(x:V)(A:Nat)(d:independent (mask A))(i:∃a∈mask A,adj x a):∃j<cap k I x,gQ D x j/\∀c∈mask A,¬lab D W x j c:=by obtain⟨g,s,hlt,_,v,y,u⟩:=vc G0 H.1 S (mask A) d x i;obtain⟨j,p,r⟩:=L8 G x (g,s) (sM.2 ⟨hlt,v,y⟩);exact⟨j,lL p (L5 G x),p,λ c S q=>p36.1 u (r▸q.2) S⟩
end
lemma xb(S:tF V)(m:Nat)(a:∀v∈S,v.1<m):∑ v∈S,2^v.1<2^m:=by induction m generalizing S with|zero=>{simp[fE.2 λ v g=>hJ _ (a v g)]}|succ m ih=>{rw[<-fS S (λ v:V=>v.1<m)];have:=ih (S.filter (λ v=>v.1<m)) (λ v g=>(mF.1 g).2);have:∑ v∈S.filter (λ v=>¬v.1<m),2^v.1<=2^m:=by{by_cases j:(S.filter (λ v=>¬v.1<m)).Nonempty;{obtain⟨p,d⟩:=j;have c:p.1=m:=by{have:=a p (mF.1 d).1;have:=(mF.1 d).2;omega};have i:S.filter (λ v=>¬v.1<m)={p}:=by{ext v;simp only[mS];exact⟨λ g=>Fin.ext (by{have:=a v (mF.1 g).1;have:=(mF.1 g).2;omega}),λ h=>h▸d⟩};rw[i,Finset.sum_singleton,c]};{rw[fN.1 j];simp}};rw[Nat.pow_succ];omega}
lemma lex_step_bit(g:G1 D k I W E F O){t:Nat}(c:t+1<k)(x:V)(a:∀y:V,x.1<y.1->(resAt D O t y↔resAt D O (t+1) y))(d:resAt D O t x):resAt D O (t+1) x:=by classical by_contra K;let C (s:Nat):=univ.filter (λ v:V=>resAt D O s v);have i:∀(s:Nat)(r:s<k),zl D (O ⟨s,r⟩)=∑ v∈C s,2^v.1:=λ s r=>by{cases X:O ⟨s,r⟩ with|none=>{have:C s=∅:=by{ext v;simp[C,resAt,X]};simp[zl,this]}|some u=>{have:C s=fM 10 D u.1:=by{ext v;simp[C,resAt,r,X]};simp[zl,yk,this]}};let A:=univ.filter (λ v:V=>resAt D O t v);let B:=univ.filter (λ v:V=>resAt D O (t+1) v);have p:∑ v∈A,2^v.1<=∑ v∈B,2^v.1:=by{rw[<-i t (by omega),<-i (t+1) c];exact g.2.2.2.2.1 ⟨t,by omega⟩ ⟨t+1,c⟩ (by simp)};rw[<-fS A (λ v=>x.1<v.1),<-fS B (λ v=>x.1<v.1)] at p;have m:A.filter (λ v=>x.1<v.1)=B.filter (λ v=>x.1<v.1):=by{ext v;simp only[A,B,mF,mU,true_and];exact⟨λ⟨Q,q⟩=>⟨(a v q).1 Q,q⟩,λ⟨Q,q⟩=>⟨(a v q).2 Q,q⟩⟩};rw[m] at p;have P:2^x.1<=∑ v∈A.filter (λ v=>¬x.1<v.1),2^v.1:=hE (f:=λ v:V=>2^v.1) (λ _ _=>nZ _) (mF.2 ⟨mF.2 ⟨mU _,d⟩,Nat.lt_irrefl _⟩);have L:=xb (B.filter (λ v=>¬x.1<v.1)) x.1 (λ v U=>by{have:=mF.1 U;have:=(mF.1 this.1).2;have:v.1≠x.1:=λ h=>K (Fin.ext h▸this);omega});omega
def b8(D:qD)(x:V)(a b:Nat):Prop:=q5 10 D a b/\x∈fM 10 D a/\x∈fM 10 D b
section
variable (Q:q0 10 D){x:V}(M:w5 10 D (q2 10 D {x})=∅){a b c:Nat}
include Q x M a b c
lemma vy(d:b8 D x a c)(g:b8 D x b c):a=b:=by have l:=d.1.2.1;have j:c-10<(tD D):=by{have:=d.1.1;omega};have m:=j6 Q M j (by simpa[Nat.add_sub_of_le l] using d.2.2);rcases d.1.2.2 with u|r<;>rcases g.1.2.2 with q|p;{exact u.symm.trans q};{exact (m.2 ⟨u.symm▸d.2.1,p.symm▸g.2.1⟩).elim};{exact (m.2 ⟨q.symm▸g.2.1,r.symm▸d.2.1⟩).elim};{exact r.symm.trans p}
lemma kb(h:RT (b8 D x) a c)(g:RT (b8 D x) b c):RT (b8 D x) a b\/RT (b8 D x) b a:=by induction h with|refl=>{exact .inr g}|@tail u c q l ih=>{rcases rK g with rfl|⟨d,r,p⟩;{exact .inl (rT q l)};{have m:u=d:=vy Q M l p;subst m;exact ih r}}
end
lemma jg(h:SL D)(a:SC D){x:V}(c:w5 10 D (q2 10 D {x})=∅):∀(d:Nat) (g:Nat) (s:Bool),g<(tD D)->(tD D)-g<=d->x∈fM 10 D (fC D (g,s))->∃e∈fD 10 D x,fM 10 D (fC D (g,s))⊆fM 10 D (fC D e)/\(e=(g,s)\/(x∈fM 10 D (10+g)/\RT (b8 D x) (10+g) (fC D e))):=by intro d;induction d with|zero=>{intro _ _ _ _ _;omega}|succ d ih=>{intro g s K P X;by_cases i:x∈fM 10 D (10+g);{have L:=j6 h.1 c K i;have u:fM 10 D (fC D (g,s))⊆fM 10 D (10+g):=by{rw[yj h.1 K L.1];cases s<;>simp[fC]};have m:10+g+1<10+(tD D):=by{have:10+g≠qb 10 D:=λ R=>wd G0 x ((a (q9 x)).1 (w3.1 (R▸i)));unfold qb at this;omega};obtain⟨H,z⟩:=fz.1 (nT nO (h.2.1 (10+g) m));simp only[qg,mF,mR] at z;obtain⟨J,p⟩:=sX z.2;have M:g<H:=by{have:=h.1 H z.1;cases J<;>simp[fC] at p<;>omega};obtain⟨e,U,q,r⟩:=ih H J z.1 (by omega) (p▸i);refine⟨e,U,u.trans (p▸q),.inr ⟨i,?_⟩⟩;rcases r with rfl|⟨y,j⟩;rw[p];exact .head ⟨⟨by omega,by omega,by simpa using z.2⟩,i,y⟩ j};{exact⟨(g,s),sM.2 ⟨K,X,i⟩,Finset.Subset.refl _,.inl rfl⟩}}
lemma rsubPair(h:SL D)(l:SC D)(d:G1 D k I W E F O){t:Nat}{x:V}(c:resAt D O t x)(hM:w5 10 D (q2 10 D {x})=∅):∃u:U0,∃ht:t<k,O ⟨t,ht⟩=some u/\∃j1 j2:Nat,j1<fF D x/\j2<fF D x/\j1≠j2/\rsub D W O t x j1/\rsub D W O t x j2/\RT (b8 D x) u.1 (fC D (W x j1))/\RT (b8 D x) u.1 (fC D (W x j2)):=by obtain⟨ht,v⟩:=c;cases p:O ⟨t,ht⟩ with|none=>{rw[p] at v;exact v.elim}|some u=>{rw[p] at v;have X:=d.2.2.1 ⟨t,ht⟩ u p;have fc:2<=fanout D u.1:=by{have:=mR.1 (p44.1 (mF.1 (mD.1 X).1).1).2;omega};obtain⟨g1,L,g2,K,R⟩:=(p46 (s:=qg D u.1)).1 (by{unfold fanout at fc;omega});simp only[qg,mF,mR] at L K;obtain⟨s1,J⟩:=sX L.2;obtain⟨s2,H⟩:=sX K.2;obtain⟨e1,hi,h3,f7⟩:=jg h l hM (tD D) g1 s1 L.1 (by omega) (J▸v);obtain⟨e2,hg,h0,f6⟩:=jg h l hM (tD D) g2 s2 K.1 (by omega) (H▸v);have h5:e1≠e2:=λ hf=>by{subst hf;rcases f7 with rfl|⟨_,g⟩<;>rcases f6 with hh|⟨_,h2⟩;{exact R (congrArg p65 hh)};{have:=qk h.1 (λ _ _ h=>h.1) h2;rw[J] at this;have:=w7 h.1 K.1 s2;omega};{subst hh;have:=qk h.1 (λ _ _ h=>h.1) g;rw[H] at this;have:=w7 h.1 L.1 s1;omega};{have hu:∀z U Z Y,z<(tD D)->U<(tD D)->z≠U->fC D (z,Z)=u.1->fC D (U,Y)=u.1->RT (b8 D x) (10+z) (10+U)->False:=λ z U Z Y fb fa f8 f5 Q h4=>by{rcases rK h4 with hf|⟨w,hw,q⟩;exact f8 (by omega);have:=qk h.1 (λ _ _ h=>h.1) hw;have:=w7 h.1 fb Z;have M:=j6 h.1 hM fa q.2.2;have m:=q.1.2.2;rw[nA] at m;cases Y<;>simp[fC] at Q<;>rcases m with hA|hB;{omega};{exact M.2 ⟨Q.symm▸v,hB.symm▸q.2.1⟩};{exact M.2 ⟨hA.symm▸q.2.1,Q.symm▸v⟩};{omega}};rcases kb h.1 hM g h2 with fe|fd;exact hu g1 g2 s1 s2 L.1 K.1 R J H fe;exact hu g2 g1 s2 s1 K.1 L.1 R.symm H J fd}};obtain⟨j1,he,h9⟩:=L8 d x e1 hi;obtain⟨j2,hd,h8⟩:=L8 d x e2 hg;have r:∀j e,j<fF D x->W x j=e->fM 10 D u.1⊆fM 10 D (fC D e)->rsub D W O t x j:=λ j e hj hwe ha=>⟨hj,λ y ⟨_,h7⟩=>⟨hj,hwe▸ha (by{rw[p] at h7;exact h7})⟩⟩;have mkRT:∀g s e,g<(tD D)->(yx D g=u.1\/yf D g=u.1)->fC D (g,s)=u.1->(e=(g,s)\/(x∈fM 10 D (10+g)/\RT (b8 D x) (10+g) (fC D e)))->RT (b8 D x) u.1 (fC D e):=λ g s e hg hq hf hc=>by{rcases hc with rfl|⟨hx,hrt⟩;{rw[hf]};{exact .head ⟨⟨by omega,by omega,by simpa using hq⟩,v,hx⟩ hrt}};exact⟨u,ht,p,j1,j2,he,hd,λ hje=>h5 (h9.symm.trans (hje▸h8)),r j1 e1 he h9 (J▸h3),r j2 e2 hd h8 (H▸h0),h9▸mkRT g1 s1 e1 L.1 L.2 J f7,h8▸mkRT g2 s2 e2 K.1 K.2 H f6⟩}
lemma rsubTwo_of(h:SL D)(l:SC D)(d:G1 D k I W E F O){t:Nat}{x:V}(c:resAt D O t x)(i:¬gR D x)(a:Nat):∃j<cap k I x,j≠a/\rsub D W O t x j:=by have hM:w5 10 D (q2 10 D {x})=∅:=g8.1 (by{unfold gR at i;omega});obtain⟨_,_,_,j1,j2,he,hd,hne,r1,r2,_,_⟩:=rsubPair h l d c hM;by_cases g:j1=a;{exact⟨j2,lL hd (L5 d x),λ hm=>hne (g.trans hm.symm),r2⟩};{exact⟨j1,lL he (L5 d x),g,r1⟩}
lemma rsubDisj_of(h:SL D)(l:SC D)(d:G1 D k I W E F O){t1 t2:Nat}{x y1 y2:V}{j:Nat}(c1:resAt D O t1 x)(c2:resAt D O t2 x)(hy1:resAt D O t1 y1)(hn2:¬resAt D O t2 y1)(hy2:resAt D O t2 y2)(hn1:¬resAt D O t1 y2)(i:¬gR D x)(hj:gQ D x j)(hr1:¬rsub D W O t1 x j)(hr2:¬rsub D W O t2 x j):5<=fF D x:=by have hM:w5 10 D (q2 10 D {x})=∅:=g8.1 (by{unfold gR at i;omega});have hsub:∀{a b},RT (b8 D x) a b->fM 10 D a⊆fM 10 D b:=λ r=>by{induction r with|refl=>{exact Finset.Subset.refl _}|@tail u v _ s ih=>{have l0:=s.1.2.1;have j0:v-10<(tD D):=by{have:=s.1.1;omega};have m:=j6 h.1 hM j0 (by simpa[Nat.add_sub_of_le l0] using s.2.2);have hv:fM 10 D v=fM 10 D (yx D (v-10))∪fM 10 D (yf D (v-10)):=(by simpa[Nat.add_sub_of_le l0] using yj h.1 j0 m.1);refine ih.trans ?_;rw[hv];rcases s.1.2.2 with hu|hu;{rw[hu];exact Finset.subset_union_left};{rw[hu];exact Finset.subset_union_right}}};obtain⟨u1,ht1,p1,a1,a2,ha1,ha2,ha12,ra1,ra2,ta1,ta2⟩:=rsubPair h l d c1 hM;obtain⟨u2,ht2,p2,b1,b2,hb1,hb2,hb12,rb1,rb2,tb1,tb2⟩:=rsubPair h l d c2 hM;have h12:∀a b,RT (b8 D x) u1.1 (fC D (W x a))->RT (b8 D x) u2.1 (fC D (W x b))->a≠b:=λ a b ta tb hab=>by{subst hab;rcases kb h.1 hM ta tb with h1|h2;{obtain⟨_,hy1m⟩:=hy1;rw[p1] at hy1m;exact hn2 ⟨ht2,by rw[p2];exact hsub h1 hy1m⟩};{obtain⟨_,hy2m⟩:=hy2;rw[p2] at hy2m;exact hn1 ⟨ht1,by rw[p1];exact hsub h2 hy2m⟩}};have:=h12 a1 b1 ta1 tb1;have:=h12 a1 b2 ta1 tb2;have:=h12 a2 b1 ta2 tb1;have:=h12 a2 b2 ta2 tb2;have:j≠a1:=λ e=>hr1 (e▸ra1);have:j≠a2:=λ e=>hr1 (e▸ra2);have:j≠b1:=λ e=>hr2 (e▸rb1);have:j≠b2:=λ e=>hr2 (e▸rb2);have:j<fF D x:=hj;omega
lemma oppSelf_of(a:q0 10 D)(c:G1 D k I W E F O)(x:V)(j:Nat):¬opp D W x j x:=by rintro⟨_,d⟩;have h:=L6 c x j;have ⟨hlt,hx1,hxn⟩:=sM.1 h;have i:=sA a h;apply hxn;rw[qm a hlt i,mI];rcases hwe:W x j with ⟨g,s⟩;rw[hwe] at hx1 d;cases s<;>simp[fC,sem_bar] at hx1 d ⊢;{exact⟨hx1,d⟩};{exact⟨d,hx1⟩}
section
variable (Q:q0 10 D)(G:G1 D k I W E F O){x y:V}{j:Nat}
include Q G x y j
lemma labOppMerge_of(c:lab D W x j y)(a:opp D W x j y):gR D y:=by rcases c with ⟨_,c⟩;rcases a with ⟨_,a⟩;have m:=L6 G x j;have i:=(sM.1 m).1;have l:y∈fM 10 D (yx D (W x j).1)/\y∈fM 10 D (yf D (W x j).1):=by{rcases hwe:W x j with ⟨g,s⟩;rw[hwe] at c a;cases s<;>simp[fC,sem_bar] at c a ⊢;exact⟨c,a⟩;exact⟨a,c⟩};exact fz.2 ⟨_,mF.2 ⟨mR.2 i,q8.2 (by{rw[qm Q i (sA Q m),mI];exact l}),q8.2 l.1,q8.2 l.2⟩⟩
lemma smateAny_of(c:lab D W x j y)(a:¬opp D W x j y):∃l<cap k I y,gQ D y l/\W y l=W x j:=by rcases c with ⟨i,c⟩;have p:=L6 G x j;have q:=(sM.1 p).1;obtain⟨l,h,m⟩:=L8 G y (W x j) (sM.2 ⟨q,c,λ r=>a ⟨i,sU Q q (sA Q p) (!(W x j).2) r⟩⟩);exact⟨l,lL h (L5 G y),h,m⟩
lemma omateAny_of(a:opp D W x j y)(c:¬lab D W x j y):∃l<cap k I y,gQ D y l/\W y l=sem_bar (W x j):=by rcases a with ⟨i,a⟩;have q:=L6 G x j;have m:=(sM.1 q).1;obtain⟨l,h,p⟩:=L8 G y (sem_bar (W x j)) (sM.2 ⟨m,a,λ u=>c ⟨i,sU Q m (sA Q q) (W x j).2 u⟩⟩);exact⟨l,lL h (L5 G y),h,p⟩
end
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O)(M:mask I=ineligSet 10 D)
include H S G M
lemma inelig_unique_slot{y:V}(d:I.testBit y.1=p63):fD 10 D y={W y 0}/\∀a,adj y a->a∈fM 10 D (fC D (sem_bar (W y 0))):=by have p:y∈ineligSet 10 D:=M▸mF.2 ⟨mU _,d⟩;obtain⟨e,_,_,_,_,m,j,_⟩:=qe G0 H S p;change fD 10 D y={e} at j;have l:=mS.1 (j▸L6 G y 0);rw[l];exact⟨j,m⟩
lemma ineligOpp_bar_eq{x y:V}(d:x≠y)(g:I.testBit y.1=p63){j:Nat}(a:opp D W x j y):sem_bar (W x j)=W y 0:=by have r:=L6 G x j;have m:=(sM.1 r).1;have q:sem_bar (W x j)∈fD 10 D y:=sM.2 ⟨m,a.2,λ z=>d (mS.1 (sP G0 H.1 S (M▸mF.2 ⟨mU _,g⟩) (sU H.1 m (sA H.1 r) (W x j).2 z)▸(sM.1 r).2.1))⟩;rwa[(inelig_unique_slot H S G M g).1,mS] at q
lemma ineligOppNF_of{x y:V}(g:x≠y)(l:I.testBit y.1=p63){j:Nat}(c:opp D W x j y):¬gT D W E x j:=by intro r;obtain⟨a,z,_⟩:=G0.2.2.2 y y;set p:=fW y a;have u:sflip p.2 (E p.1)∈fD 10 D y:=by{simpa[p,(wt y a z).1] using (L9 G p.2 p.1).1};rw[(inelig_unique_slot H S G M l).1,mS] at u;exact r.2 p.1 (!p.2) (by rw[sflip_not,u,<-ineligOpp_bar_eq H S G M g l c,sem_bar_bar])
lemma ineligOppInelig_of{i j:V}(g:I.testBit i.1=p63)(l:I.testBit j.1=p63)(_hne:i≠j):¬opp D W i 0 j:=by rintro⟨_,r⟩;have y:i∈ineligSet 10 D:=M▸mF.2 ⟨mU _,g⟩;have u:j∈ineligSet 10 D:=M▸mF.2 ⟨mU _,l⟩;obtain⟨a,v,_⟩:=G0.2.2.2 i i;have p:=(inelig_unique_slot H S G M g).2 a v;rw[sP G0 H.1 S u r,mS] at p;subst a;exact (j5 G0 H S v).elim (sE.1 y) (sE.1 u)
end
lemma ineligFilter_of(h:SL D)(m:SC D)(H:Bzero 10 D=0)(r:G1 D k I W E F O)(J:mask I=ineligSet 10 D){i y d:V}(K:I.testBit i.1=p63)(j:¬adj i y)(p:adj i d)(q:opp D W i 0 y):∃l<cap k I d,aempty D W E (fW i d).1 d l/\gT D W E d l/\¬lab D W d l y/\∀x2:V,adj i x2->lab D W d l x2/\¬opp D W d l x2:=by have fj:i∈ineligSet 10 D:=J▸mF.2 ⟨mU _,K⟩;have hx:=zv G0 h m H fj;obtain⟨L,hq,fb,he,hg,_,h6,_⟩:=qe G0 h m fj;have g3:W i 0=L:=by{simpa[fD,h6] using (L6 r) i 0};have U:(E (fW i d).1).1=L.1:=by{have hW:=(L9 r (fW i d).2 (fW i d).1).1;rw[(wt i d p).1] at hW;simp only[fD,h6,mS] at hW;simpa[sflip] using congrArg p65 hW};have M:∀w,fO D (λ _:V=>p55) w=p55:=λ w=>if z:w<10+(tD D) then jy h.1 _ (λ _=>p55) (λ _ _=>rfl) (λ j _=>by cases gZ D j<;>rfl) w z else z0 D _ w (by omega);have Y:RT (q5 10 D) i.1 (10+L.1):=(yu (λ _ _ h=>h.1) (wn h.1 (q9 i) (λ _=>p55) i (λ _ hk=>by simp[q9,hk]) (fC D L) (by{rw[w3.1 (he▸m0 i),M];decide}))).tail (qs hq L.2);have h7:q7 10 D (10+L.1) (qb 10 D):=by{rcases j8 h.1 hx Y with g9|⟨fy,_⟩;{have:=qk h.1 (λ _ _ h=>h) g9;have:=lP h.2.2;rw[show 10+L.1=qb 10 D by{unfold qb at *;omega}];exact .refl};{exact fy}};have hf:fO D (q1 i y) (10+L.1)=p63:=by{rw[qd h.1 _ hq L.2,fb,gop_true,q3 h.1 (he▸m0 i) (by simp[q1]),q3 h.1 (by simpa[g3,sem_bar] using q.2) (by simp[q1])];rfl};have f4:fO D (q1 i y) (qb 10 D)=p55:=by{cases hv:fO D (q1 i y) (qb 10 D);rfl;exfalso;obtain⟨a,b,fc,ha,hb⟩:=(m _).1 hv;simp only[q1,bO,dT] at ha hb;rcases ha with rfl|rfl<;>rcases hb with rfl|rfl;{exact G0.2.1 _ fc};{exact j fc};{exact j (G0.1 _ _ fc)};{exact G0.2.1 _ fc}};have fk:∀{a b},q7 10 D a b->fO D (q1 i y) a=p63->fO D (q1 i y) b=p55->∃u v,q7 10 D a u/\q5 10 D u v/\fanout D u=1/\fO D (q1 i y) u=p63/\fO D (q1 i y) v=p55:=by{intro a b gc;induction gc using rI with|refl=>{intro h1 h2;rw[h1] at h2;cases h2}|@head a c f7 _ ih=>{intro ha hb;cases hs:fO D (q1 i y) c;{exact⟨a,c,.refl,f7.1,f7.2,ha,hs⟩};{obtain⟨u,v,ga,B⟩:=ih hs hb;exact⟨u,v,.head f7 ga,B⟩}}};obtain⟨u,v,h5,ff,fa,fr,h9⟩:=fk h7 hf f4;obtain⟨g,s,P,rfl,rfl⟩:=y3.1 ff;have h4:gZ D g=p63/\fO D (q1 i y) (fC D (g,!s))=p55:=by{rw[qd h.1 _ P s,fr] at h9;cases fs:gZ D g;simp[fs] at h9;exact⟨rfl,by simpa[fs,gop_true] using h9⟩};have f9:L.1<g:=by{have:=qk h.1 (λ _ _ h=>h.1) h5;have:=w7 h.1 P s;omega};have Z:q7 10 D i.1 (10+L.1):=by{rcases j9 Y with ge|⟨b,gd,fx⟩;exact ge;exact absurd (ze G0 h.1 m fj gd fx▸y7 h.1 H fx) gk};have Q:q7 10 D i.1 (fC D (g,s)):=Z.trans h5;have hy:=Q.tail ⟨qs P s,fa⟩;have X:fM 10 D (fC D (g,s))=∅:=by{have hn:=kh h.1 (q9 i) (λ _=>p55) i (λ _ hk=>by simp[q9,hk]) (10+L.1) (fC D (g,s)) (vn h.1 Z (qk h.1 (λ _ _ h=>h.1) h5)) (by{rw[M];exact p54.2 (λ ht=>nE i (hg▸w3.2 ht))});rw[M] at hn;exact fE.2 λ z hz=>p58 ((w3.1 hz).symm.trans ((mS.1 (yw G0 h.1 m i _ (wp h.1 Q) hz))▸hn))};have f1:∀x2,adj i x2->x2∈fM 10 D (fC D (g,!s))/\x2∉fM 10 D (10+g):=λ x2 fd=>by{have hp:fO D (q1 i x2) (10+g)≠fO D (q9 x2) (10+g):=λ fl=>by{have fu:=k6 h.1 (q1 i x2) (q9 x2) i (λ _ hk=>by simp[q1,q9,hk]) (10+g) (wp h.1 hy) fl;rw[(m _).2 (yv fd),p54.2 (λ ht=>wd G0 x2 ((m _).1 ht))] at fu;cases fu};have fh:=x9 h.1 (q9 x2) (q1 i x2) (kg (by simp[q1])) (10+g);have ⟨R,hh⟩:fO D (q1 i x2) (10+g)=p63/\fO D (q9 x2) (10+g)=p55:=by{cases f6:fO D (q1 i x2) (10+g)<;>cases f5:fO D (q9 x2) (10+g)<;>first|exact⟨rfl,rfl⟩|exact absurd (f6.trans f5.symm) hp|exact absurd (fh f5) (by{rw[f6];decide})};rw[qd h.1 _ P s,h4.1,gop_true,bA] at R;have fn:=vd h.1 i P (!s) (by simpa[p60] using Q) (by simpa[p60] using fa) (q1 i x2) (q9 x2) (λ _ hk=>by simp[q1,q9,hk]);exact⟨w3.2 (fn▸R.2),λ hm=>p58 ((w3.1 hm).symm.trans hh)⟩};obtain⟨l,h3,hl⟩:=L8 r d (g,!s) (sM.2 ⟨P,(f1 d p).1,(f1 d p).2⟩);have hd:gU D W d l:=⟨h3,by{rw[hl,sK];exact X}⟩;exact⟨l,lL h3 (L5 r d),⟨⟨h3,by{rw[U,hl];exact f9}⟩,hd⟩,ka (L9 r) hd,λ⟨_,hj⟩=>p58 ((q3 h.1 (hl▸hj) (x:=q1 i y) (by simp[q1])).symm.trans h4.2),λ x2 fd=>⟨⟨h3,hl▸(f1 x2 fd).1⟩,λ⟨_,ho⟩=>nE x2 (by{rw[hl,sK,X] at ho;exact ho})⟩⟩
end
def es(D:qD)(a:EI->qO)(s:Bool)(e:EI)(x:V):Prop:=x∈fM 10 D (fC D (sflip s (a e)))
def lt_e(a:EI->qO)(d c:EI):Prop:=(a d).1<(a c).1
def sgate(a:EI->qO)(d c:EI):Prop:=(a d).1=(a c).1
def jh(D:qD)(u v:V)(g:Nat):Prop:=g<(tD D)/\gZ D g=p63/\∃s:Bool,u∈fM 10 D (fC D (g,s))/\v∉fM 10 D (fC D (g,s))/\v∈fM 10 D (fC D (g,!s))/\u∉fM 10 D (fC D (g,!s))
def fZ(D:qD)(a:EI->qO)(e:EI):Prop:=∃g,g≠(a e).1/\jh D (ep0 e) (ep1 e) g
abbrev has_sec:=fZ
def sec_pair(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(d g:Nat):Prop:=gQ D (ep0 e) d/\gQ D (ep1 e) g/\(a (ep0 e) d).1≠(c e).1/\a (ep1 e) g=sem_bar (a (ep0 e) d)
def wy(D:qD)(x:V->Bool)(d c:Nat):Prop:=RT (λ a b=>q5 10 D a b/\fO D x a=p63/\fO D x b=p63) d c
def zm(D:qD)(d c:Nat):Prop:=RT (λ a b=>q5 10 D a b/\fM 10 D a=∅/\fanout D a=1) d c
def xv(D:qD)(b:Nat):Prop:=fM 10 D b=∅/\2<=fanout D b
def gS(D:qD)(a:Nat):Prop:=zm D a (qb 10 D)/\fM 10 D (qb 10 D)=∅
abbrev stay_empty:=gS
def hit_b(D:qD)(a:Nat):Prop:=Bzero 10 D=1/\∃b0,zm D a b0/\xv D b0
def gX(D:qD)(a:Nat)(z:V):Prop:=∃r,zm D a r/\z∈fM 10 D r/\∀t∈fM 10 D r,z<=t
abbrev pick_z:=gX
def h0Prop(D:qD)(a:V->Nat->qO)(c:EI->qO)(d:EI)(z:V)(l:Nat):Prop:=after D a c d z l/\(opp D a z l (ep0 d)\/opp D a z l (ep1 d))
def kc(D:qD)(c:EI->qO)(d:EI)(a b:V)(h:Nat):Prop:=h<(tD D)/\wy D (q1 (ep0 d) (ep1 d)) (10+(c d).1) (10+h)/\fO D (q1 a b) (10+h)=p55
noncomputable def wi(D:qD)(c:EI->qO)(d:EI)(a b:V):Nat:=open Classical in if hex:∃h,kc D c d a b h then p22 hex else 0
def bc(D:qD)(c:EI->qO)(d:EI)(a b:V)(g:EI):Prop:=fZ D c d\/(fO D (q1 a b) (10+(c d).1)=p63/\wy D (q1 (ep0 d) (ep1 d)) (10+(c d).1) (10+(c g).1)/\wy D (q1 (ep0 d) (ep1 d)) (10+(c g).1) (10+wi D c d a b)/\(c g).1<wi D c d a b)
def efhProp(D:qD)(c:V->Nat->qO)(d:EI->qO)(h:EI)(a b:V)(i:EI)(g:V)(l:Nat):Prop:=after D c d i g l/\¬opp D c g l a/\¬opp D c g l b/\(opp D c g l (ep0 h)\/opp D c g l (ep1 h))
def eseProp(D:qD)(c:EI->qO)(h:EI)(a b:V)(i:EI)(g:V)(d:EI):Prop:=lt_e c i d/\(es D c p55 d g\/es D c p63 d g)/\bc D c h a b d
def mescProp(D:qD)(w:V->Nat->qO)(e:EI->qO)(d:EI)(am:Nat)(z:V)(l:Nat):Prop:=(opp D w z l (ep0 d)\/opp D w z l (ep1 d))/\∃e':EI,!am.testBit e'.1/\∃s:Bool,ra D w e s e' z l
section
open Finset (min'_mem min'_le)
variable {D:qD} {k I:Nat} {W:V->Nat->qO} {E:EI->qO} {F:V->Nat} {O:Fin k->Option U0}
abbrev AR:=wy
abbrev EC:=zm
abbrev s2:=@q1 10
lemma sF(h:q0 10 D){u a b:V}{w:Nat}(m:u∈fM 10 D w)(e:u=a\/u=b)(v:fO D (s2 a b) w=p55):False:=by cases (q3 h m (x:=s2 a b) (by rcases e with rfl|rfl<;>simp[q1])).symm.trans v
lemma ji(a:q0 10 D){u v:V}{g:Nat}(c:jh D u v g):∃s:Bool,(g,s)∈fD 10 D u/\(g,!s)∈fD 10 D v/\u∈fM 10 D (fC D (g,s))/\v∈fM 10 D (fC D (g,!s)):=by obtain⟨d,p,s,m,i,l,j⟩:=c;exact⟨s,sM.2 ⟨d,m,λ h=>j (sU a d p (!s) h)⟩,sM.2 ⟨d,l,λ h=>i (sU a d p s h)⟩,m,l⟩
lemma secNotRa0_of{e:EI}{a c:Nat}(d:sec_pair D W E e a c):¬ra D W E p55 e (ep0 e) a:=λ g=>d.2.2.1 (by rw[g.2,sflip_false])
lemma secNotRa1_of{e:EI}{c a:Nat}(d:sec_pair D W E e c a):¬ra D W E p63 e (ep1 e) a:=λ g=>by have i:(W (ep1 e) a).1=(W (ep0 e) c).1:=by{rw[d.2.2.2];rfl};have h:(W (ep1 e) a).1=(E e).1:=by{rw[g.2,sflip_true];rfl};exact d.2.2.1 (i.symm.trans h)
lemma secEq_of{e:EI}{c a:Nat}(d:sec_pair D W E e c a)(y:V):(lab D W (ep1 e) a y↔opp D W (ep0 e) c y)/\(lab D W (ep0 e) c y↔opp D W (ep1 e) a y):=by have _:=d.1;have _:=d.2.1;constructor<;>(simp only[lab,opp,d.2.2.2,sem_bar_bar];tauto)
section
variable (Q:q0 10 D)
include Q
lemma hasSecAny_of(a:G1 D k I W E F O){e:EI}(c:fZ D E e):∃ju<cap k I (ep0 e),∃jv<cap k I (ep1 e),sec_pair D W E e ju jv:=by obtain⟨g,m,r⟩:=c;obtain⟨s,l,j,_,_⟩:=ji Q r;obtain⟨ju,i,p⟩:=L8 a (ep0 e) (g,s) l;obtain⟨jv,h,q⟩:=L8 a (ep1 e) (g,!s) j;exact⟨ju,lL i (L5 a _),jv,lL h (L5 a _),i,h,by rw[p];exact m,by rw[p,q];rfl⟩
lemma fG(a:gP D E)(e:EI):jh D (ep0 e) (ep1 e) (E e).1:=by have d:=a p55 e;have h:=a p63 e;rw[sflip_false] at d;rw[sflip_true] at h;obtain⟨g,j,_⟩:=sM.1 d.1;obtain⟨_,i,_⟩:=sM.1 h.1;exact⟨g,sA Q d.1,(E e).2,by simpa[endpoint] using j,by simpa[endpoint] using d.2,by simpa[endpoint,sem_bar] using i,by simpa[endpoint,sem_bar] using h.2⟩
lemma qp{x:V->Bool}{a b:Nat}(h:AR D x a b):a<=b:=qk Q (λ _ _ d=>d.1) h
lemma vq(u v:V):∀w:Nat,fO D (s2 u v) w=p63->u∉fM 10 D w->v∉fM 10 D w->∃g,jh D u v g/\AR D (s2 u v) (10+g) w:=by intro w;induction w using sI with|ind w ih=>{intro q l i;by_cases A:w<10;{rw[qa D _ w A] at q;simp only[q1,bO,dT] at q;rcases q with L|L;exact absurd (w3.2 (by{rw[qa D _ w A,q9,L];simp})) l;exact absurd (w3.2 (by{rw[qa D _ w A,q9,L];simp})) i};by_cases m:w-10<(tD D);{set j:=w-10;let X:=yx D j;let Y:=yf D j;have c:w=10+j:=by{omega};have:=Q j m;have y:=c▸qs m p55;have r:=c▸qs m p63;have p:=q;rw[c,qu Q _ j m] at q;cases P:gZ D j;{rw[P,gop_false,bO] at q;rw[c,yj Q m P,mN,not_or] at l i;rcases q with z|d;obtain⟨g,K,J⟩:=ih (X) (by omega) z l.1 i.1;exact⟨g,K,J.tail ⟨y,z,p⟩⟩;obtain⟨g,K,J⟩:=ih (Y) (by omega) d l.2 i.2;exact⟨g,K,J.tail ⟨r,d,p⟩⟩};{rw[P,gop_true,bA] at q;by_cases U:u∉fM 10 D (X)/\v∉fM 10 D (X);{obtain⟨g,K,J⟩:=ih (X) (by omega) q.1 U.1 U.2;exact⟨g,K,J.tail ⟨y,q.1,p⟩⟩};by_cases R:u∉fM 10 D (Y)/\v∉fM 10 D (Y);{obtain⟨g,K,J⟩:=ih (Y) (by omega) q.2 R.1 R.2;exact⟨g,K,J.tail ⟨r,q.2,p⟩⟩};rw[c,qm Q m P,mI] at l i;have ha':u∈fM 10 D (X)\/v∈fM 10 D (X):=by{tauto};have hb':u∈fM 10 D (Y)\/v∈fM 10 D (Y):=by{tauto};refine⟨j,⟨m,P,?_⟩,c▸.refl⟩;rcases ha' with M|z;{have H:=λ h=>l ⟨M,h⟩;have d:=hb'.resolve_left H;exact⟨p55,M,λ h=>i ⟨h,d⟩,d,H⟩};{have d:=λ h=>i ⟨z,h⟩;have H:=hb'.resolve_right d;exact⟨p63,H,d,z,λ h=>l ⟨h,H⟩⟩}}};{rw[z0 D _ w (by omega)] at q;cases q}}
lemma y8{e:EI}(a:¬fZ D E e){w:Nat}(h:fO D (s2 (ep0 e) (ep1 e)) w=p63)(d:ep0 e∉fM 10 D w)(c:ep1 e∉fM 10 D w):AR D (s2 (ep0 e) (ep1 e)) (10+(E e).1) w:=by obtain⟨g,m,l⟩:=vq Q (ep0 e) (ep1 e) w h d c;have:g=(E e).1:=by{by_contra j;exact a ⟨g,j,m⟩};rwa [this] at l
lemma jt(c:SC D){e:EI}(a:¬fZ D E e):AR D (s2 (ep0 e) (ep1 e)) (10+(E e).1) (qb 10 D):=by have g:=qn G0 c;exact y8 Q a ((c _).2 (yv (xk e))) (by rw[g];exact nE _) (by rw[g];exact nE _)
lemma y6{x:V->Bool}{z:V}{a b:Nat}(h:AR D x a b)(c:z∈fM 10 D a)(d:z∉fM 10 D b):∃g s,g<(tD D)/\10+g<=b/\fO D x (10+g)=p63/\AR D x a (fC D (g,s))/\z∈fM 10 D (fC D (g,s))/\z∉fM 10 D (10+g)/\AR D x (10+g) b:=by induction h using rI with|refl=>{exact absurd c d}|@head u v l p ih=>{by_cases m:z∈fM 10 D v;{obtain⟨g,s,P,M,L,K,J,H,y⟩:=ih m;exact⟨g,s,P,M,L,rH l K,J,H,y⟩};{obtain⟨g,s,r,rfl,rfl⟩:=y3.1 l.1;exact⟨g,s,r,qp Q p,l.2.2,rR,c,m,p⟩}}
lemma w8{a b:Nat}(c:EC D a b):a<=b:=qk Q (λ _ _ h=>h.1) c
end
section
variable {R:Nat->Nat->Prop}(Q:q0 10 D)(Y:∀x y,R x y->q5 10 D x y){a c q:Nat}(M:EC D a c)(N:RT R a q)
include R Q Y a c q M N
lemma y9:RT R c q\/(EC D a q/\EC D q c/\q≠c):=by induction M using rI with|refl=>{exact .inl N}|@head u v j m ih=>{rcases rC N with rfl|⟨r,p,l⟩;{have:=wb Q j.1;have:=w8 Q m;exact .inr ⟨rR,rH j m,by omega⟩};{have:r=v:=qj (Y _ _ p) j.1 j.2.2;subst this;rcases ih l with K|⟨J,H,z⟩;exact .inl K;exact .inr ⟨rH j J,H,z⟩}}
lemma qx(h:c<=q):RT R a c/\RT R c q:=by induction M using rI with|refl=>{exact⟨rR,N⟩}|@head u v m r ih=>{rcases rC N with rfl|⟨z,l,p⟩;{have:=wb Q m.1;have:=w8 Q r;omega};{have:z=v:=qj (Y _ _ l) m.1 m.2.2;subst this;obtain⟨J,H⟩:=ih p;exact⟨rH l J,H⟩}}
lemma qr(i:q<=c):EC D a q:=by rcases y9 Q Y M N with m|⟨p,_,_⟩;{have:=qk Q Y m;have l:q=c:=by{omega};rw[l];exact M};{exact p}
end
section
variable (Q:q0 10 D)
include Q
lemma z7{a d c:Nat}(m:EC D a d)(l:EC D a c)(i:¬(fM 10 D d=∅/\fanout D d=1))(g:¬(fM 10 D c=∅/\fanout D c=1)):d=c:=by rcases y9 Q (λ _ _ h=>h.1) m l with v|⟨_,u,q⟩;{rcases rC v with rfl|⟨_,p,_⟩;{rfl};{exact absurd p.2 i}};{rcases rC u with r|⟨_,p,_⟩;{exact absurd r q};{exact absurd p.2 g}}
lemma pickUniq_of{w:Nat}{c a:V}(i:gX D w c)(g:gX D w a):c=a:=by obtain⟨y,u,l,p⟩:=i;obtain⟨v,r,j,m⟩:=g;have q:=z7 Q u r (λ h=>by rw[h.1] at l;exact nE _ l) (λ h=>by rw[h.1] at j;exact nE _ j);subst q;exact le_antisymm (p a j) (m c l)
end
lemma sameStay_of{d c:EI}(a:sgate E d c)(g:gS D (10+(E d).1)):gS D (10+(E c).1):=by unfold sgate at a;rw[<-a];exact g
lemma samePick_of{d c:EI}{z:V}(a:sgate E d c)(g:gX D (10+(E d).1) z):gX D (10+(E c).1) z:=by unfold sgate at a;rw[<-a];exact g
section
variable (H:SL D)(S:SC D)
include H S
lemma yq(c:Bzero 10 D<=1):∀d w,w<10+(tD D)->qb 10 D-w=d->gS D w\/hit_b D w\/∃z:V,gX D w z:=by intro d;induction d using sI with|ind d ih=>{intro w P M;by_cases j:(fM 10 D w).Nonempty;{exact .inr (.inr ⟨(fM 10 D w).min' j,w,rR,min'_mem _ j,min'_le _⟩)};rw[fN] at j;by_cases p:w=qb 10 D;{exact .inl ⟨p▸rR,qn G0 S⟩};have:=lP H.2.2;have q:w+1<10+(tD D):=by{unfold qb at p;omega};have L:=H.2.1 w q;by_cases v:2<=fanout D w;{exact .inr (.inl ⟨by{by_cases J:Bzero 10 D=0;exact absurd (y7 H.1 J v) (j▸gk);omega},w,rR,j,v⟩)};have m:fanout D w=1:=by{omega};obtain⟨g,i⟩:=fz.1 (show 0<(qg D w).card by{unfold fanout at m;omega});simp only[qg,mF,mR] at i;have l:q5 10 D w (10+g):=⟨by omega,by omega,by{rw[nA];exact i.2}⟩;have:=wb H.1 l;have y:q5 10 D w (10+g)/\fM 10 D w=∅/\fanout D w=1:=⟨l,j,m⟩;rcases ih (qb 10 D-(10+g)) (by{unfold qb at M ⊢;omega}) (10+g) (by omega) rfl with ⟨hch,hso⟩|⟨u,b0,hcb,his⟩|⟨z,r,hcr,hzr,hmin⟩;{exact .inl ⟨.head y hch,hso⟩};{exact .inr (.inl ⟨u,b0,.head y hcb,his⟩)};{exact .inr (.inr ⟨z,r,.head y hcr,hzr,hmin⟩)}}
lemma stepAny_of(c:Bzero 10 D<=1)(g:gP D E)(a:EI):gS D (10+(E a).1)\/hit_b D (10+(E a).1)\/∃z:V,gX D (10+(E a).1) z:=yq H S c _ (10+(E a).1) (by have i:=(sM.1 (g p55 a).1).1;rw[sflip_false] at i;omega) rfl
lemma stepAny0_of(g:Bzero 10 D=0)(d:gP D E)(a:EI):gS D (10+(E a).1)\/∃z:V,gX D (10+(E a).1) z:=by rcases stepAny_of H S (by omega) d a with i|l|j;{exact .inl i};{exact absurd l.1 (by omega)};{exact .inr j}
lemma pickZH0_of(j:G1 D k I W E F O){c:EI}{z:V}(d:gX D (10+(E c).1) z)(a:¬fZ D E c):∃l<cap k I z,h0Prop D W E c z l:=by classical set u:=ep0 c;set v:=ep1 c;obtain⟨r,hcr,hzr,_⟩:=d;have L:=(qx H.1 (λ _ _ d=>d.1) hcr (jt H.1 S a) (by{have:=wx hzr;have:=lP H.2.2;unfold qb;omega})).2;have hb:∃g,g<(tD D)/\fO D (s2 u v) (10+g)=p63/\z∉fM 10 D (10+g)/\∃s:Bool,AR D (s2 u v) r (fC D (g,s))/\z∈fM 10 D (fC D (g,s)):=by{obtain⟨g,s,h1,_,h3,h4,h5,h6,_⟩:=y6 H.1 L hzr (by{rw[qn G0 S];exact nE _});exact⟨g,h1,h3,h6,s,h4,h5⟩};set g0:=p22 hb;obtain⟨m,J,A,s,K,p⟩:=p24 hb;have hW:(g0,s)∈fD 10 D z:=sM.2 ⟨m,p,A⟩;have M:=sA H.1 hW;obtain⟨l,q,h7⟩:=L8 j z (g0,s) hW;have Z:r<10+g0:=lt_of_le_of_lt (qp H.1 K) (w7 H.1 m s);refine⟨l,lL q (L5 j z),⟨q,by{have:=w8 H.1 hcr;rw[h7];dsimp;omega}⟩,?_⟩;set y:=fC D (g0,!s);rw[show (opp D W z l u\/opp D W z l v)↔(u∈fM 10 D y\/v∈fM 10 D y) by simp[opp,gQ,q,h7,sem_bar,y]];by_contra Y;push Not at Y;have h8:fO D (s2 u v) y=p63:=by{rw[qd H.1 _ m s,M,gop_true,bA] at J;exact J.2};have R:z∉fM 10 D y:=λ Q=>A <| by{rw[qm H.1 m M,mI];cases s<;>simp only[fC,y,Bool.not_false,p61] at p Q ⊢;exact⟨p,Q⟩;exact⟨Q,p⟩};rcases y9 H.1 (λ _ _ d=>d.1) hcr (y8 H.1 a h8 Y.1 Y.2) with ha|⟨_,h0,U⟩;{obtain⟨g1,s1,h1,h2,h3,h4,h5,h6,_⟩:=y6 H.1 ha hzr R;have hk:y<10+p22 hb:=w7 H.1 m (!s);exact p23 hb (by omega:g1<p22 hb) ⟨h1,h3,h6,s1,h4,h5⟩};{rcases rC h0 with he|⟨_,h9,X⟩;exact U he;have:=w8 H.1 (qj h9.1 (qs m (!s)) h9.2.2▸X);omega}
end
lemma ve(d:SC D){a b:V}(c:¬adj a b):fO D (s2 a b) (qb 10 D)=p55:=by cases j:fO D (s2 a b) (qb 10 D) with|false=>{rfl}|true=>{exfalso;obtain⟨x,y,g,i,h⟩:=(d (s2 a b)).1 j;simp only[q1,bO,dT] at i h;rcases i with rfl|rfl<;>rcases h with rfl|rfl;{exact G0.2.1 _ g};{exact c g};{exact c (G0.1 _ _ g)};{exact G0.2.1 _ g}}
section
variable (H:SL D)(S:SC D){d:EI}{a b:V}(U:¬adj a b)(N:¬fZ D E d)
include H S d a b U N
lemma ya:kc D E d a b (wi D E d a b)/\∀w<10+wi D E d a b,AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) w->fO D (s2 a b) w=p63:=by classical have v:=lP H.2.2;have q:10+((tD D)-1)=qb 10 D:=by{unfold qb;omega};have p:∃g,kc D E d a b g:=⟨(tD D)-1,by omega,q▸jt H.1 S N,q▸ve S U⟩;rw[show wi D E d a b=p22 p by{unfold wi;exact hD p}];refine⟨p24 p,λ w z u=>?_⟩;have:=qp H.1 u;have m:w-10<p22 p:=by{omega};have l:10+(w-10)=w:=by{omega};cases y:fO D (s2 a b) w;exact absurd ⟨lt_trans m (p24 p).1,l.symm▸u,l.symm▸y⟩ (p23 p m);rfl
lemma zo{s:Bool}(g:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) (fC D (wi D E d a b,s))):gZ D (wi D E d a b)=p63/\a∉fM 10 D (fC D (wi D E d a b,!s))/\b∉fM 10 D (fC D (wi D E d a b,!s))/\(ep0 d∈fM 10 D (fC D (wi D E d a b,!s))\/ep1 d∈fM 10 D (fC D (wi D E d a b,!s))):=by set y:=wi D E d a b;obtain⟨⟨m,u,z⟩,hmin⟩:=ya H S U N;have p:=w7 H.1 m s;have hvf':=z;rw[qd H.1 _ m s,hmin _ p g] at hvf';have J:gZ D y=p63:=by{cases A:gZ D y;rw[A,gop_false] at hvf';simp at hvf';rfl};have l:fO D (s2 a b) (fC D (y,!s))=p55:=by{rw[J,gop_true,p64] at hvf';exact hvf'};have q:fO D (s2 (ep0 d) (ep1 d)) (10+y)=p63:=by{rcases rK u with M|⟨_,_,P⟩;exact absurd (lt_of_le_of_lt (qp H.1 g) p) (M▸lt_irrefl _);exact P.2.2};have r:fO D (s2 (ep0 d) (ep1 d)) (fC D (y,!s))=p63:=by{rw[qd H.1 _ m s,J,gop_true,bA] at q;exact q.2};refine⟨J,λ R=>sF H.1 R (.inl rfl) l,λ Q=>sF H.1 Q (.inr rfl) l,by_contra λ v=>?_⟩;push Not at v;exact p58 ((hmin _ (w7 H.1 m (!s)) (y8 H.1 N r v.1 v.2)).symm.trans l)
lemma x3(A:fO D (s2 a b) (10+(E d).1)=p63):gZ D (wi D E d a b)=p63:=by obtain⟨⟨_,m,q⟩,_⟩:=ya H S U N;rcases rK m with u|⟨_,r,v⟩;{rw[<-u,q] at A;cases A};{obtain⟨g,s,_,y,p⟩:=y3.1 v.1;have z:g=wi D E d a b:=by{omega};rw[z] at p;subst p;exact (zo H S U N r).1}
end
lemma maskClosure_of(H:SL D)(S:SC D)(B:Bzero 10 D=0)(G:G1 D k I W E F O){d:EI}{am cm:Nat}(hd:am.testBit d.1=p63)(hnsec:¬fZ D E d)(hstay:∀e:EI,am.testBit e.1=p63->¬gS D (10+(E e).1))(hpick:∀e:EI,am.testBit e.1=p63->∀z:V,cm.testBit z.1=p55->¬gX D (10+(E e).1) z)(hfree:∀z:V,cm.testBit z.1=p63->∀l<cap k I z,¬gT D W E z l)(hopp:∀z:V,cm.testBit z.1=p63->∀l<cap k I z,∀y:V,cm.testBit y.1=p63->¬opp D W z l y)(hesc:∀z:V,cm.testBit z.1=p63->∀l<cap k I z,¬mescProp D W E d am z l):False:=by set x:=s2 (ep0 d) (ep1 d);let Good (w:Nat):Prop:=(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D w)\/(∃e:EI,am.testBit e.1=p63/\EC D (10+(E e).1) w);have hstep:{a b:Nat}->{e:EI}->am.testBit e.1=p63->EC D (10+(E e).1) a->q5 10 D a b->(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D a)\/EC D (10+(E e).1) b:=by{intro a b e he hza hab;rcases stepAny0_of H S B (L9 G) e with hs|⟨z,hzx⟩;{exact absurd hs (hstay e he)};{have hzc:cm.testBit z.1=p63:=by{cases hcb:cm.testBit z.1;{exact absurd hzx (hpick e he z hcb)};{rfl}};obtain⟨r,hzr,hzmr,_⟩:=hzx;rcases y9 H.1 (λ _ _ h=>h.1) hzr hza with hra|⟨_,har,hne⟩;{rcases rC hra with rfl|⟨_,hr,_⟩;{exact .inl ⟨z,hzc,hzmr⟩};{rw[hr.2.1] at hzmr;exact absurd hzmr (nE z)}};{rcases rC har with rfl|⟨c,ha,_⟩;{exact absurd rfl hne};{have hcb:c=b:=qj ha.1 hab ha.2.2;exact .inr (hza.tail ⟨hab,ha.2.1,ha.2.2⟩)}}}};have hGood:∀w,AR D x (10+(E d).1) w->Good w:=by{intro w;induction w using sI with|ind b ih=>{intro har;rcases rK har with rfl|⟨a,hara,hstep_ab⟩;{exact .inr ⟨d,hd,rR⟩};{have hga:Good a:=ih a (wb H.1 hstep_ab.1) hara;have hfrom_z:(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D a)->Good b:=by{rintro⟨z,hzc,hza⟩;obtain⟨g,s,hg,rfl,rfl⟩:=y3.1 hstep_ab.1;by_cases hzb:z∈fM 10 D (10+g);{exact .inl ⟨z,hzc,hzb⟩};{have hW:(g,s)∈fD 10 D z:=sM.2 ⟨hg,hza,hzb⟩;have hA:=sA H.1 hW;obtain⟨l,hl,hWl⟩:=L8 G z (g,s) hW;have hlcap:l<cap k I z:=lL hl (L5 G z);have hnf:=hfree z hzc l hlcap;have ⟨e',s',he'⟩:∃e' s',W z l=sflip s' (E e'):=by{unfold gT at hnf;push Not at hnf;exact hnf hl};have hge':(E e').1=g:=by{have:=congrArg p65 (hWl.symm.trans he');cases s'<;>simpa[sflip] using this.symm};set y:=fC D (g,!s);have hOy:fO D x y=p63:=by{have hOb:=hstep_ab.2.2;rw[qd H.1 x hg s,hA,gop_true,bA] at hOb;exact hOb.2};have hy_eq:fC D (sem_bar (W z l))=y:=by{rw[hWl];rfl};by_cases hopp_uv:ep0 d∈fM 10 D y\/ep1 d∈fM 10 D y;{have hopp':opp D W z l (ep0 d)\/opp D W z l (ep1 d):=hopp_uv.imp (λ h=>⟨hl,hy_eq.symm▸h⟩) (λ h=>⟨hl,hy_eq.symm▸h⟩);have ham':am.testBit e'.1=p63:=by{cases hbit:am.testBit e'.1;{exact absurd ⟨hopp',e',by simp[hbit],s',hl,he'⟩ (hesc z hzc l hlcap)};{rfl}};exact .inr ⟨e',ham',by{rw[hge'];exact rR}⟩};{push Not at hopp_uv;have hgy:Good y:=ih y (w7 H.1 hg (!s)) (y8 H.1 hnsec hOy hopp_uv.1 hopp_uv.2);rcases hgy with ⟨z',hz'c,hz'y⟩|⟨e'',he'',hze''⟩;{exact absurd ⟨hl,hy_eq.symm▸hz'y⟩ (hopp z hzc l hlcap z' hz'c)};{rcases hstep he'' hze'' (qs hg (!s)) with ⟨z'',hz''c,hz''y⟩|hzb'';{exact absurd ⟨hl,hy_eq.symm▸hz''y⟩ (hopp z hzc l hlcap z'' hz''c)};{exact .inr ⟨e'',he'',hzb''⟩}}}}};rcases hga with hza|⟨e,he,hza⟩;{exact hfrom_z hza};{rcases hstep he hza hstep_ab.1 with hza'|hzb';{exact hfrom_z hza'};{exact .inr ⟨e,he,hzb'⟩}}}}};rcases hGood (qb 10 D) (jt H.1 S hnsec) with ⟨z,_,hzq⟩|⟨e,he,hze⟩;{rw[qn G0 S] at hzq;exact nE z hzq};{exact hstay e he ⟨hze,qn G0 S⟩}
lemma bcInit_of(h:SL D)(i:SC D)(j:gP D E){c:EI}{a b:V}(d:¬adj a b)(g:(es D E p55 c a/\es D E p63 c b)\/(es D E p55 c b/\es D E p63 c a)):bc D E c a b c:=by by_cases q:fZ D E c;{exact .inl q};{right;have p:=fG h.1 j c;have l:fO D (s2 a b) (10+(E c).1)=p63:=by{rw[qd h.1 _ p.1 (E c).2,p.2.1,gop_true];have K:fC D ((E c).1,(E c).2)=fC D (sflip p55 (E c)):=by{simp[sflip_false]};have J:fC D ((E c).1,!(E c).2)=fC D (sflip p63 (E c)):=by{simp[sflip_true,sem_bar]};rw[K,J];rcases g with ⟨y,v⟩|⟨v,y⟩<;>{rw[q3 h.1 y (by simp[q1]),q3 h.1 v (by simp[q1])];rfl}};obtain⟨⟨_,m,r⟩,_⟩:=ya h i d q;have H:=qp h.1 m;have z:(E c).1≠wi D E c a b:=λ u=>by{rw[u,r] at l;cases l};exact⟨l,rR,m,by omega⟩}
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O){d:EI}{a b:V}(U:¬adj a b)
include H S G d a b U
lemma zu(g:¬fZ D E d){s:Bool}(j:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) (fC D (wi D E d a b,s)))(i:fM 10 D (fC D (wi D E d a b,s))=∅):∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,gQ D z l/\(W z l).1=wi D E d a b/\gU D W z l:=by set M:=wi D E d a b;have v:=(ya H S U g).1.1;obtain⟨ht,X,B,R⟩:=zo H S U g j;have A:fM 10 D (10+M)=∅:=fE.2 λ c P=>nE _ (i▸sU H.1 v ht s P);have y:∀{z:V},z=ep0 d\/z=ep1 d->z∈fM 10 D (fC D (M,!s))->∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,gQ D z l/\(W z l).1=M/\gU D W z l:=λ {z} L r=>by{obtain⟨l,u,Q⟩:=L8 G z (M,!s) (sM.2 ⟨v,r,A▸nE _⟩);exact⟨z,L,λ Y=>X (by{rw[Y] at r;exact r}),λ Y=>B (by{rw[Y] at r;exact r}),l,lL u (L5 G z),u,by rw[Q],u,by{rw[Q,sK];exact i}⟩};exact R.elim (y (.inl rfl)) (y (.inr rfl))
lemma qq(j:¬fZ D E d){m:Nat}(_hws_lt:m<10+wi D E d a b)(i:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) m)(A:AR D (s2 (ep0 d) (ep1 d)) m (10+wi D E d a b))(r:EC D m (10+wi D E d a b)):∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,gQ D z l/\(W z l).1=wi D E d a b/\gU D W z l:=by rcases rK r with Q|⟨p,K,y⟩;{omega};{obtain⟨g,s,_,M,B⟩:=y3.1 y.1;have P:g=wi D E d a b:=by{omega};rw[P] at B;exact zu H S G U j (B▸i.trans (qx H.1 (λ _ _ L=>L.1) K A (le_of_lt (wb H.1 y.1))).1) (B▸y.2.1)}
lemma vf(i:¬fZ D E d)(p:fO D (s2 a b) (10+(E d).1)=p63){m:Nat}(_hws_lt:m<10+wi D E d a b)(q:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) m)(j:AR D (s2 (ep0 d) (ep1 d)) m (10+wi D E d a b)){c:V}(v:gX D m c):EC D m (10+wi D E d a b)\/(c≠a/\c≠b/\gR D c)\/(∃l<cap k I c,gQ D c l/\m<10+(W c l).1/\((¬opp D W c l a/\¬opp D W c l b/\(opp D W c l (ep0 d)\/opp D W c l (ep1 d)))\/gT D W E c l))\/(∃e3:EI,m<10+(E e3).1/\(es D E p55 e3 c\/es D E p63 e3 c)/\bc D E d a b e3):=by set hs:=wi D E d a b;obtain⟨r,hcr,hd,_⟩:=v;by_cases hm:10+hs<=r;{exact .inl (qr H.1 (λ _ _ hp=>hp.1) hcr j hm)};obtain⟨X,Z⟩:=qx H.1 (λ _ _ hp=>hp.1) hcr j (by omega);by_cases J:c∈fM 10 D (10+hs);{obtain⟨⟨Q,_,h3⟩,_⟩:=ya H S U i;have hf:=mI.1 (qm H.1 Q (x3 H S U i p)▸J);exact .inr (.inl ⟨λ he=>sF H.1 J (.inl he) h3,λ he=>sF H.1 J (.inr he) h3,fz.2 ⟨hs,mF.2 ⟨mR.2 Q,q8.2 J,q8.2 hf.1,q8.2 hf.2⟩⟩⟩)};obtain⟨g,s,L,_,h8,Y,M,h7,h5⟩:=y6 H.1 Z hd J;have hW:(g,s)∈fD 10 D c:=sM.2 ⟨L,M,h7⟩;obtain⟨l,A,P⟩:=L8 G c (g,s) hW;have B:m<10+g:=by{have:=w8 H.1 hcr;have:=qp H.1 Y;have:=w7 H.1 L s;omega};have K:=(q.trans X).trans Y;by_cases ha:g=hs;{subst ha;obtain⟨_,hl,hk,hi⟩:=zo H S U i K;exact .inr (.inr (.inl ⟨l,lL A (L5 G c),A,P▸B,.inl (by simpa[opp,gQ,A,P,sem_bar] using And.intro hl (And.intro hk hi))⟩))};by_cases h6:gT D W E c l;{exact .inr (.inr (.inl ⟨l,lL A (L5 G c),A,P▸B,.inr h6⟩))};have ⟨e3,s3,hb⟩:∃e3 s3,W c l=sflip s3 (E e3):=by{unfold gT at h6;push Not at h6;exact h6 A};have h2:(E e3).1=g:=by{simpa[sflip,P] using (congrArg p65 hb).symm};have h4:fO D (s2 (ep0 d) (ep1 d)) (fC D (g,s))=p63:=by{rw[qd H.1 _ L s,sA H.1 hW,gop_true,bA] at h8;exact h8.1};have R:es D E s3 e3 c:=by{unfold es;rw[<-hb,P];exact M};exact .inr (.inr (.inr ⟨e3,by omega,by{cases s3;exact .inl R;exact .inr R},.inr ⟨p,h2.symm▸K.tail ⟨qs L s,h4,h8⟩,h2.symm▸h5,by omega⟩⟩))
lemma bcStay_of{j:EI}(i:bc D E d a b j)(g:gS D (10+(E j).1)):fZ D E d\/∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,aempty D W E j z l:=by rcases i with q|⟨_,K,r,v⟩;{exact .inl q};{by_cases q:fZ D E d;{exact .inl q};{right;have:=(ya H S U q).1.1;have:=lP H.2.2;obtain⟨z,Q,P,M,l,y,u,J,L⟩:=qq H S G U q (by omega) K r (qr H.1 (λ _ _ R=>R.1) g.1 r (by{unfold qb;omega}));exact⟨z,Q,P,M,l,y,⟨u,J▸v⟩,L⟩}}
lemma bcPick_of{A:EI}{c:V}(m:bc D E d a b A)(j:gX D (10+(E A).1) c):fZ D E d\/(∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,aempty D W E A z l)\/(c≠a/\c≠b/\gR D c)\/(∃l<cap k I c,efhProp D W E d a b A c l\/afree D W E A c l)\/(∃e3:EI,e3≠A/\eseProp D E d a b A c e3):=by rcases m with v|⟨Q,B,y,J⟩;{exact o1 v};{by_cases v:fZ D E d;{exact o1 v};{rcases vf H S G U v Q (by omega) B y j with K|hm|⟨l,u,r,h2,R⟩|⟨e3,C,X,Z⟩;{obtain⟨z,P,h1,h0,l,u,r,M,Y⟩:=qq H S G U v (by omega) B y K;exact o2 (o1 ⟨z,P,h1,h0,l,u,⟨r,by{rw[M];exact J}⟩,Y⟩)};{exact o2 (o2 (o1 hm))};{exact o2 (o2 (o2 (o1 ⟨l,u,R.elim (λ⟨ha,hb,P⟩=>o1 ⟨⟨r,by omega⟩,ha,hb,P⟩) (λ h3=>o2 ⟨⟨r,by omega⟩,h3⟩)⟩)))};{exact o2 (o2 (o2 (o2 ⟨e3,λ he=>by{rw[he] at C;omega},by{unfold lt_e;omega},X,Z⟩)))}}}
end
end
end
end
abbrev CellKill (k I m s:Nat):Prop:=∃t c x:List Nat,∀v:Nat->Bool,(∀u,Rup.enS k I m s t c x u=true->Rup.Holds v (Rup.expS k I m t c x u))->False
namespace P3
abbrev CK:=CellKill
open DagTools
open Rup
open PriorG11.SharedCases renaming GoodLayout->V0,SLive->V1,autPerm->V2,ineligOpp_bar_eq->V3,lt_e->V4,maskImage->V5,pinSlots->V6,pinTarget->V7,relabelEdge_fst->V8,relabel_residualUnits_mem->V9,resAt->Va,sflip->Vb,sflip_not->Vc
open DagTools renaming StrictLive->Vd,ineligSet->Ve,residualUnits->Vf,sem_bar->Vg,sem_bar_bar->Vh,sem_mem_W->Vi
open Rup renaming avoidMask->Vj,edgeIdxS->Vk,eligNbrsN->Vl,ineligNbrsN->Vm,nbrsN->Vn
open List renaming mem_map->Vo,length_map->Vp,range->Vq
open Nat renaming reduceLT->Vr
abbrev Ei:=EdgeIdx
abbrev Ws:=V->Nat->Slot
abbrev Es:=Ei->Slot
abbrev Os k:=Fin k->Option (Σ _:Nat,Nat)
abbrev LN:=List Nat
abbrev F(x:Nat):V:=Fin.ofNat 10 x
abbrev J(e:Nat):Ei:=Fin.ofNat 14 e
noncomputable def bP(P:Prop):Bool:=@decide P (Classical.propDecidable P)
@[local simp] lemma bt{P:Prop}:bP P=true <->P:=@decide_eq_true_iff P (Classical.propDecidable P)
@[local simp] lemma bf{P:Prop}:bP P=false <->¬P:=@decide_eq_false_iff_not P (Classical.propDecidable P)
lemma sA{a b}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma sD{p} [Decidable p]:(decide p=true)=p:=decide_eq_true_eq
lemma sQ{α} [BEq α] [LawfulBEq α] {a b:α}:(a==b)=true <->a=b:=beq_iff_eq
lemma sN{α} [BEq α] [LawfulBEq α] {a b:α}:(a != b)=true <->a≠b:=bne_iff_ne
lemma sB{a}:((!a)=true)=(a=false):=Bool.not_eq_true' a
lemma sC{a b c:Prop}:(a/\b)/\c <->a/\b/\c:=and_assoc
lemma sT{α}{a b:α}:(if True then a else b)=a:=ite_true a b
lemma sF{α}{a b:α}:(if False then a else b)=b:=ite_false a b
abbrev mo{a b:Nat} (h:a<b):=Nat.mod_eq_of_lt h
abbrev T{P Q:Prop} (h:P <->Q):=h.1
abbrev W{P Q:Prop} (h:P <->Q):=h.2
lemma f0v{x}(h:x<10):(F x).1=x:=mo h
lemma f0n{x y}(hx:x<10)(hy:y<10)(h:x≠y):F x≠F y:=λ q=>h (by rw[<-f0v hx,<-f0v hy,q])
lemma f0e(x:V):F x.1=x:=Fin.ext (mo x.2)
lemma f4e(e:Ei):J e.1=e:=Fin.ext (mo e.2)
lemma aM(n r:Nat):r&&&(2^n-1)<2^n:=by rw[Nat.and_two_pow_sub_one_eq_mod];exact Nat.mod_lt _ (Nat.two_pow_pos n)
lemma a1(r:Nat):r&&&1<2:=aM 1 r
lemma a4(r:Nat):r&&&15<16:=aM 4 r
lemma a6(r:Nat):r&&&63<64:=aM 6 r
lemma bnot1{s}(h:s<2):((1-s)==1)=!(s==1):=by rcases (by omega:s=0\/s=1) with rfl|rfl<;>rfl
abbrev mF{α p} [DecidablePred p] {s:Finset α} {a}:=@Finset.mem_filter α p _ s a
abbrev mU{α} [Fintype α]:=@Finset.mem_univ α _
abbrev mG{α β} [DecidableEq β] {f:α->β} {s a}:=@Finset.mem_image α β _ f s a
abbrev lR{n m}:=@List.mem_range n m
abbrev lF{α p} {l:List α} {a}:=@List.mem_filter α p l a
lemma finE{n x}(h:x<n):∃u:Fin n,u.1=x:=⟨⟨x,h⟩,rfl⟩
lemma eN{e}(h:e<14):F (ep0N e)=ep0 (J e)/\F (ep1N e)=ep1 (J e)/\ep0N e<10/\ep1N e<10:=by obtain⟨u,rfl⟩:=finE h;revert u;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
abbrev e0q{e} (h:e<14):=(eN h).1
abbrev e1q{e} (h:e<14):=(eN h).2.1
abbrev e0l{e} (h:e<14):=(eN h).2.2.1
abbrev e1l{e} (h:e<14):=(eN h).2.2.2
lemma enq{s e}(d:s<2)(he:e<14):F (epN s e)=endpoint (s==1) (J e):=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE he;revert u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma enl{s e}(he:e<14):epN s e<10:=by unfold epN;split<;>[exact e0l he;exact e1l he]
lemma aBi{x y}(d:x<10)(hy:y<10):adjB x y=true <->adj (F x) (F y):=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE hy;revert u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma cNq(k I){x}(d:x<10):capN k I x=cap k I (F x):=by unfold capN inIB cap;simp[mo d]
lemma c5{k I x j}(h:j<capN k I x)(_:k<=3:=by omega):j<5:=by unfold capN at h;split at h<;>omega
lemma c5V{k I j}{z:V}(h:j<cap k I z)(_:k<=3:=by omega):j<5:=c5 (by rw[cNq k I z.2,f0e];exact h)
lemma iB{I x}(d:x<10)(h:inIB I x=true):I.testBit (F x).1=true:=by rw[f0v d];exact h
lemma nB{I x}(d:x<10)(h:inIB I x=false):I.testBit (F x).1=false:=by rw[f0v d];exact h
lemma nMap(x:V):(Vn x.1).map F=(List.finRange 10).filter (λ y=>(neigh x).testBit y.1):=by revert x;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma nLt{i n}(d:i<10)(h3:n<3)(hn:n<(Vn i).length):(Vn i).getD n 0<10/\adj (F i) (F ((Vn i).getD n 0))/\n<3:=by have q:∀u:V,∀k:Fin 3,k.1<(Vn u.1).length->(Vn u.1).getD k.1 0<10/\adj u (F ((Vn u.1).getD k.1 0)):=(by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel);obtain⟨u,rfl⟩:=finE d;have k:=(q u) ⟨n,h3⟩ hn;exact⟨k.1,(f0e u).symm▸k.2,h3⟩
lemma eSq{x y}(d:x<10)(hy:y<10)(f:adj (F x) (F y)):(Vk x y).1<14/\(Vk x y).2<2/\J (Vk x y).1=(edgeOfPair (F x) (F y)).1/\((Vk x y).2==1)=(edgeOfPair (F x) (F y)).2:=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE hy;revert f u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma aMi{a}(d:a<16):independent (mask (Vj a)):=by obtain⟨u,rfl⟩:=finE d;revert u;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma aMn{x a}(d:x<10)(f:a<16)(h:((Vj a)&&&neighN x)≠0):∃v∈mask (Vj a),adj (F x) v:=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE f;revert h u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma nMem{x}(d:x<10):∀y∈Vn x,y<10:=by obtain⟨u,rfl⟩:=finE d;revert u;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma nF{x}(d:x<10)(p:Nat->Bool)(q:V->Bool)(hp:∀y<10,p y=q (F y)):((Vn x).filter p).map F=(List.finRange 10).filter (λ y=>(neigh (F x)).testBit y.1&&q y):=by have f:=nMap (F x);simp only[Fin.val_ofNat,mo d] at f;rw[show (Vn x).filter p=(Vn x).filter (q ∘ F) from List.filter_congr λ y hy=>hp y (nMem d y hy),<-List.filter_map,f,List.filter_filter];exact List.filter_congr λ _ _=>Bool.and_comm _ _
lemma iNq I {x}(hx:x<10):(Vm I x).map F=ineligNbrs I (F x):=nF hx (inIB I) (λ y=>I.testBit y.1) λ y hy=>by simp[inIB,mo hy]
lemma eNq I {x}(hx:x<10):(Vl I x).map F=eligNbrs I (F x):=nF hx (λ y=>!inIB I y) (λ y=>!I.testBit y.1) λ y hy=>by simp[inIB,mo hy]
lemma p3c{k m}(hk:k<=3)(d:m<1<<<k):((Finset.univ:Finset (Fin k)).filter (λ t=>m.testBit t.1)).card=pop3 m:=by have q:∀a:Fin 4,∀b:Fin 8,b.1<1<<<a.1->((Finset.univ:Finset (Fin a.1)).filter (λ t=>b.1.testBit t.1)).card=pop3 b.1:=(by decide +kernel);exact q ⟨k,by omega⟩ ⟨m,by interval_cases k<;>omega⟩ d
namespace EP
lemma sL(a b:Nat):a+b-a=b:=Nat.add_sub_cancel_left a b
lemma d1{a b m:Nat}(h:b<m:=by omega):(a*m+b)/m=a:=by rw[Nat.mul_comm,Nat.mul_add_div (by omega),Nat.div_eq_of_lt h,Nat.add_zero]
lemma m1{a b m:Nat}(h:b<m:=by omega):(a*m+b) % m=b:=by rw[Nat.mul_comm,Nat.mul_add_mod,mo h]
abbrev C b (P Q:Nat->Prop) (i:Nat):=cond (i.blt b) (P i) (Q i)
lemma cT{a b}{P Q:Nat->Prop}(h:a<b:=by omega):C b P Q a=P a:=by simp[C,Nat.blt_eq,h]
lemma cF{a b}{P Q:Nat->Prop}(h:b<=a:=by omega):C b P Q a=Q a:=by simp[C,Nat.blt_eq,Nat.not_lt.2 h]
def s0 n (f:Nat->Prop) i:=f (i-n)
def s1 n u (f:Nat->Nat->Prop) i:=f ((i-n)/u) ((i-n) % u)
def s2 n u v (f:Nat->Nat->Nat->Prop) i:=f ((i-n)/v/u) ((i-n)/v % u) ((i-n) % v)
def s3 n u v w (f:Nat->Nat->Nat->Nat->Prop) i:=f ((i-n)/w/v/u) ((i-n)/w/v % u) ((i-n)/w % v) ((i-n) % w)
lemma b0 a {n f}:s0 n f (n+a)=f a:=by rw[s0,sL]
lemma b1 a b {n u f}(_:b<u:=by omega):s1 n u f (n+a*u+b)=f a b:=by rw[s1,Nat.add_assoc,sL,d1,m1]
lemma b2 a b c {n u v f}(_:b<u/\c<v:=by omega):s2 n u v f (n+(a*u+b)*v+c)=f a b c:=by rw[s2,Nat.add_assoc,sL,d1,m1,d1,m1]
lemma b3 a b c d {n u v w f}(_:b<u/\c<v/\d<w:=by omega):s3 n u v w f (n+((a*u+b)*v+c)*w+d)=f a b c d:=by rw[s3,Nat.add_assoc,sL,d1,m1,d1,m1,d1,m1]
lemma l{i b}{P Q:Nat->Prop}{R}(h:P i=R)(_:i<b:=by omega):C b P Q i=R:=(cT (a:=i) (b:=b)).trans h
lemma r{i b}{P Q:Nat->Prop}{R}(h:Q i=R)(_:b<=i:=by omega):C b P Q i=R:=(cF (a:=i) (b:=b)).trans h
abbrev U3{α} (t:LN) d (f:Ei->V->V->α):=let v:=untriple t d;f (J v.1) (F v.2.1) (F v.2.2)
abbrev Uc{α} (t c:LN) (f:Ei->V->V->Ei->V->α) d:=let u:=unctx c d;U3 t u.1 f (J u.2.1) (F u.2.2)
abbrev Um{α} (b:LN) a (f:Ei->Nat->α):=let u:=unmask b a;f (J u.1) u.2.1
abbrev eP0 D {k} w (o:Os k):=C 1080 (C 550 (C 50 (λ i=>V1 D (F (i/5)) (i % 5)) (s2 50 5 10 λ x j c=>lab D w (F x) j (F c))) (C 1050 (s2 550 5 10 λ x j c=>opp D w (F x) j (F c)) (s1 1050 10 λ t x=>Va D o t (F x)))) (C 1480 (C 1180 (s1 1080 10 λ x y=>Together D (F x) (F y)) (s2 1180 10 10 λ t x y=>Va D o t (F x)/\¬Va D o t (F y))) (C 1500 (s1 1480 10 λ t x=>∀v:V,x<=v.1->(Va D o t v <->Va D o (t+1) v)) (C 1510 (s0 1500 λ x=>has_merge D (F x)) (s2 1510 10 5 λ t x j=>rsub D w o t (F x) j))))
abbrev eP1 D w e:=C 3636 (C 3340 (C 1940 (s2 1660 14 10 λ s a x=>es D e (s==1) (J a) (F x)) (s3 1940 14 10 5 λ s a x j=>ra D w e (s==1) (J a) (F x) j)) (C 3390 (s1 3340 5 λ x j=>free_slot D w e (F x) j) (C 3440 (s1 3390 5 λ x j=>empty_opp D w (F x) j) (s1 3440 14 λ a b=>e (J a)=e (J b))))) (C 4224 (C 3832 (s1 3636 14 λ a b=>e (J a)=Vg (e (J b))) (C 4028 (s1 3832 14 λ a b=>sgate e (J a) (J b)) (s1 4028 14 λ a b=>V4 e (J a) (J b)))) (C 4924 (s2 4224 10 5 λ a x j=>after D w e (J a) (F x) j) (C 4938 (s0 4924 λ a=>has_sec D e (J a)) (s2 4938 5 5 λ a u v=>sec_pair D w e (J a) u v))))
abbrev eP2 D w e t:=C 7556 (C 6702 (C 5988 (s2 5288 10 5 λ a x j=>afree D w e (J a) (F x) j) (C 6688 (s2 5988 10 5 λ a x j=>aempty D w e (J a) (F x) j) (s0 6688 λ a=>stay_empty D (10+(e (J a)).1)))) (C 6716 (λ _=>False) (C 6856 (s1 6716 10 λ a z=>pick_z D (10+(e (J a)).1) (F z)) (s2 6856 10 5 λ a z l=>h0Prop D w e (J a) (F z) l)))) (C 7720 (λ _=>False) (C 7742 (λ _=>False) (C 7966 (s1 7742 14 λ d a=>U3 t d (bc D e) (J a)) (λ _=>False))))
abbrev eP3 D w e t c (b:LN):=C 10334 (C 9118 (C 8798 (s2 7998 16 5 λ x a j=>V1 D (F x) j/\∀y∈mask (Vj a),¬lab D w (F x) j y) (s1 8798 5 λ d l=>Uc t c (efhProp D w e) d l)) (C 10014 (s1 9118 14 λ d a=>Uc t c (eseProp D e) d (J a)) (s2 10014 10 5 λ a z l=>Um b a (mescProp D w e) (F z) l))) (C 13730 (C 11230 (λ _=>False) (s3 11230 5 10 5 λ x j y l=>V1 D (F x) j/\V1 D (F y) l/\w (F y) l=w (F x) j)) (C 16230 (s3 13730 5 10 5 λ x j y l=>V1 D (F x) j/\V1 D (F y) l/\w (F y) l=Vg (w (F x) j)) (s3 16230 10 3 5 λ a y n l=>let x:=(Vn a).getD n 0;aempty D w e (J (Vk a x).1) (F x) l/\free_slot D w e (F x) l/\¬lab D w (F x) l (F y)/\∀z:V,adj (F a) z->lab D w (F x) l z)))
def eP(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k):Nat->Prop:=C 5288 (C 1660 (eP0 D w o) (eP1 D w e)) (C 7998 (eP2 D w e t) (eP3 D w e t c b))
lemma p0(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP0 D w o n=P)(eq:i=n:=by rfl)(_:n<1660:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cT,cT,h]
lemma p1(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP1 D w e n=P)(eq:i=n:=by rfl)(_:1660<=n/\n<5288:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cT,cF,h]
lemma p2(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP2 D w e t n=P)(eq:i=n:=by rfl)(_:5288<=n/\n<7998:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cF,cT,h]
lemma p3(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP3 D w e t c b n=P)(eq:i=n:=by rfl)(_:7998<=n:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cF,cF,h]
lemma symM{P:Nat->Nat->Prop}(s:∀a b,P a b->P b a){x y}:P (min x y) (max x y) <->P x y:=by by_cases h:x<=y;{simp[Nat.min_eq_left h,Nat.max_eq_right h]};{simp only[Nat.min_eq_right (by omega:y<=x),Nat.max_eq_left (by omega:y<=x)];exact⟨s _ _,s _ _⟩}
end EP
noncomputable def trP(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat):Bool:=bP (EP.eP D w e t c b o i)
section Ev
open EP
variable {D:Dag} {w:Ws} {e:Es} {t c b:LN} {k:Nat} {o:Os k}
lemma v0{x j}(_:x<10/\j<5:=by constructor<;>first|assumption|omega):eP D w e t c b o (fLive x j) <->V1 D (F x) j:=by rw[fLive,eP,cT,cT,eP0,cT,cT,cT,d1,m1]
abbrev v1{x j y} (_:x<10/\j<5/\y<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p0 D w e t c b o (fLab x j y) (l (l (r (b2 x j y))))
abbrev v2{x j y} (_:x<10/\j<5/\y<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p0 D w e t c b o (fOpp x j y) (l (r (l (b2 x j y))))
abbrev v3{a x} (_:a<3/\x<10:=by omega):=p0 D w e t c b o (fRes a x) (l (r (r (b1 a x))))
abbrev v4{x y} (_:x<10/\y<10:=by omega):=(p0 D w e t c b o (fCommon x y) (r (l (l (b1 (min x y) (max x y)))))).trans (symM (P:=λ a b=>Together D (F a) (F b)) λ _ _ ⟨z,p,q⟩=>⟨z,q,p⟩)
abbrev v5{a x y} (_:a<3/\x<10/\y<10:=by omega):=p0 D w e t c b o (fDiff a x y) (r (l (r (b2 a x y))))
abbrev v6{a x} (_:a<2/\x<10:=by omega):=p0 D w e t c b o (fEqGe a x) (r (r (l (b1 a x))))
abbrev v7{x} (_:x<10:=by first|assumption|omega):=p0 D w e t c b o (fHm x) (r (r (r (l (b0 x)))))
abbrev v8{a x j} (_:a<3/\x<10/\j<5:=by omega):=p0 D w e t c b o (fRsub a x j) (r (r (r (r (b2 a x j)))))
abbrev v9{s a x} (_:s<2/\a<14/\x<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (fEs s a x) (l (l (l (b2 s a x))))
abbrev u0{s a x j} (_:s<2/\a<14/\x<10/\j<5:=by refine⟨?_,?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (fRa s a x j) (l (l (r (b3 s a x j))))
abbrev u1{x j} (_:x<10/\j<5:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (fFree x j) (l (r (l (b1 x j))))
abbrev u2{x j} (_:x<10/\j<5:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (fEmpty x j) (l (r (r (l (b1 x j)))))
abbrev u3{a d} (_:a<14/\d<14:=by omega):=p1 D w e t c b o (fGate a d) (l (r (r (r (b1 a d)))))
abbrev u4{a d} (_:a<14/\d<14:=by omega):=p1 D w e t c b o (fGflip a d) (r (l (l (b1 a d))))
abbrev u5{a d} (_:a<14/\d<14:=by omega):=(p1 D w e t c b o (fSgate a d) (r (l (r (l (b1 (min a d) (max a d))))))).trans (symM (P:=λ a b=>sgate e (J a) (J b)) λ _ _=>Eq.symm)
abbrev u6{a d} (_:a<14/\d<14:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (fLt a d) (r (l (r (r (b1 a d)))))
abbrev u7{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (fAfter a x j) (r (r (l (b2 a x j))))
abbrev u8{a} (_:a<14:=by first|assumption|omega):=p1 D w e t c b o (fHsec a) (r (r (r (l (b0 a)))))
abbrev u9{a u v} (_:a<14/\u<5/\v<5:=by omega):=p1 D w e t c b o (fSecp a u v) (r (r (r (r (b2 a u v)))))
abbrev t0{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p2 D w e t c b o (fAfree a x j) (l (l (l (b2 a x j))))
abbrev t1{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p2 D w e t c b o (fAempty a x j) (l (l (r (l (b2 a x j)))))
abbrev t2{a} (_:a<14:=by first|assumption|omega):=p2 D w e t c b o (fStay a) (l (l (r (r (b0 a)))))
abbrev t4{a z} (_:a<14/\z<10:=by constructor<;>first|assumption|omega):=p2 D w e t c b o (fPick a z) (l (r (r (l (b1 a z)))))
abbrev t5{a z l0} (_:a<14/\z<10/\l0<5:=by omega):=p2 D w e t c b o (fH0 a z l0) (l (r (r (r (b2 a z l0)))))
abbrev y2{d a} (_:d<16/\a<14:=by constructor<;>first|assumption|omega):=p2 D w e t c b o (fBc d a) (r (r (r (l (b1 d a)))))
abbrev y4{x a j} (_:x<10/\a<16/\j<5:=by omega):=p3 D w e t c b o (fAvoid x a j) (l (l (l (b2 x a j))))
abbrev y5{d l0} (_:d<64/\l0<5:=by constructor<;>first|assumption|omega):=p3 D w e t c b o (fEfh d l0) (l (l (r (b1 d l0))))
abbrev y6{d a} (_:d<64/\a<14:=by constructor<;>first|assumption|omega):=p3 D w e t c b o (fEse d a) (l (r (l (b1 d a))))
abbrev y7{a z l0} (_:a<6/\z<10/\l0<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p3 D w e t c b o (fMesc a z l0) (l (r (r (b2 a z l0))))
abbrev y9{x j y l0} (_:x<10/\j<5/\y<10/\l0<5:=by omega):=p3 D w e t c b o (fSmate x j y l0) (r (l (r (b3 x j y l0))))
abbrev x0{x j y l0} (_:x<10/\j<5/\y<10/\l0<5:=by omega):=p3 D w e t c b o (fOmate x j y l0) (r (r (l (b3 x j y l0))))
abbrev x1{a y n l0} (_:a<10/\y<10/\n<3/\l0<5:=by omega):=p3 D w e t c b o (fIfilt a y n l0) (r (r (r (b3 a y n l0))))
abbrev Hp(P:Nat->Prop):=Holds (λ i=>bP (P i))
section Hc
variable {P:Nat->Prop}
lemma R{a}(h:P a):Hp P [(a,true)]:=⟨_,.head _,bt.2 h⟩
lemma j0{a}(h:¬P a):Hp P [(a,false)]:=⟨_,.head _,bf.2 h⟩
lemma G{a c}(h:P a->Hp P c):Hp P ((a,false)::c):=(Classical.em (P a)).elim (λ q=>let ⟨l,hl,hy⟩:=h q;⟨l,.tail _ hl,hy⟩) (λ q=>⟨_,.head _,bf.2 q⟩)
lemma jT{a c}(h:¬P a->Hp P c):Hp P ((a,true)::c):=(Classical.em (P a)).elim (λ q=>⟨_,.head _,bt.2 q⟩) (λ q=>let ⟨l,hl,hy⟩:=h q;⟨l,.tail _ hl,hy⟩)
abbrev B{a b} (h:P a->P b):=G λ q=>R (h q)
abbrev Z{a b} (h:P a->¬P b):=G λ q=>j0 (h q)
abbrev j3{a b c} (h:P a->P b->P c):=G λ p=>B (h p)
abbrev k3{a b c} (h:P a->P b->¬P c):=G λ p=>Z (h p)
abbrev jFT{a b c} (h:P a->¬P b->Hp P c):=G λ p=>jT (h p)
abbrev jFF{a b c} (h:P a->P b->Hp P c):=G λ p=>G (h p)
abbrev jTT{a b c} (h:¬P a->¬P b->Hp P c):=jT λ p=>jT (h p)
abbrev jFFT{a b c d} (h:P a->P b->¬P c->Hp P d):=G λ p=>jFT (h p)
lemma cb{a b}{p q:Prop}(ha:P a <->p)(hb:P b <->q)(f:p->q):Hp P [(a,false),(b,true)]:=B λ h=>hb.2 (f (ha.1 h))
lemma cz{a b}{p q:Prop}(ha:P a <->p)(hb:P b <->q)(f:p->¬q):Hp P [(a,false),(b,false)]:=Z λ h k=>f (ha.1 h) (hb.1 k)
lemma c3{a b c}{p q r:Prop}(ha:P a <->p)(hb:P b <->q)(hc:P c <->r)(f:p->q->r):Hp P [(a,false),(b,false),(c,true)]:=j3 λ h k=>hc.2 (f (ha.1 h) (hb.1 k))
lemma jI{a b c}{p:Bool}(h:P a->(P b <->P c)):Hp P [(a,false),(b,p),(c,!p)]:=G λ q=>match p with|false=>G λ r=>R ((h q).1 r)|true=>jT λ r=>j0 λ s=>r ((h q).2 s)
lemma jQ{a b c}{p:Bool}(h:(P a <->P b)->P c):Hp P [(a,p),(b,p),(c,true)]:=by cases p;{exact G λ a=>G λ b=>R (h ⟨λ _=>b,λ _=>a⟩)};{exact jT λ a=>jT λ b=>R (h ⟨λ x=>absurd x a,λ x=>absurd x b⟩)}
lemma jL{c1 c2}:Hp P c1->Hp P (c1++c2)|⟨l,hl,hy⟩=>⟨l,List.mem_append_left _ hl,hy⟩
lemma jR{c1 c2}:Hp P c2->Hp P (c1++c2)|⟨l,hl,hy⟩=>⟨l,List.mem_append_right _ hl,hy⟩
lemma jG{n} {f:Nat->Nat}:(∃j<n,P (f j))->Hp P ((Vq n).map λ j=>(f j,true))
 | ⟨j,hj,q⟩=>⟨_,Vo.2 ⟨j,lR.2 hj,rfl⟩,bt.2 q⟩
lemma jF2{n} {f g:Nat->Nat}:(∃j<n,P (f j)\/P (g j))->Hp P ((Vq n).flatMap λ j=>[(f j,true),(g j,true)])
 | ⟨j,hj,h⟩=>h.elim (λ p=>⟨(f j,true),List.mem_flatMap.2 ⟨j,lR.2 hj,by simp⟩,bt.2 p⟩) (λ p=>⟨(g j,true),List.mem_flatMap.2 ⟨j,lR.2 hj,by simp⟩,bt.2 p⟩)
end Hc
lemma jM{m x}(hk:k<=3)(hx:x<10)(h:∃i:Fin k,m.testBit i.1=true/\Va D o i.1 (F x)):Holds (trP D w e t c b o) (maskRes k m x):=by obtain⟨⟨i,d⟩,f,j⟩:=h;have q:=W (v3 (D:=D) (w:=w) (e:=e) (t:=t) (c:=c) (b:=b) (o:=o)) j;unfold maskRes;rcases (by omega:i=0\/i=1\/i=2) with rfl|rfl|rfl;{exact jL (jL (by simp[d,f];exact R q))};{exact jL (jR (by simp[d,f];exact R q))};{exact jR (by simp[d,f];exact R q)}
lemma jU{I eo x y}{f:Nat->Nat->Nat}(d:eo<14)(h:∃z:V,(z=ep0 (J eo)\/z=ep1 (J eo))/\z≠F x/\z≠F y/\∃l<cap k I z,eP D w e t c b o (f z.1 l)):Holds (trP D w e t c b o) (uvSlots k I (ep0N eo) (ep1N eo) x y λ z l=>(f z l,true)):=by obtain⟨z,n,m,j,l,hl,i⟩:=h;have p u (hu:u<10) (he:F u=z):Holds (trP D w e t c b o) (if u != x&&u != y then (Vq (capN k I u)).map λ l=>(f u l,true) else []):=by{have ha:u≠x:=λ q=>m (by rw[<-he,q]);have v:u≠y:=λ q=>j (by rw[<-he,q]);simp[ha,v];exact jG ⟨l,by rw[cNq k I hu,he];exact hl,by rw[<-he,f0v hu] at i;exact i⟩};rcases n with rfl|rfl;{exact jL (p _ (e0l d) (e0q d))};{exact jR (p _ (e1l d) (e1q d))}
end Ev
def MOk(D:Dag):Nat->Prop
 | 0=>True
 | 1=>Bzero 10 D=0
 | _=>False
def SOk(_D:Dag) (_e:Es) {k} (_o:Os k):Nat->Prop
 | 0=>True
 | _=>False
lemma mIn{D I x}(q:mask I=Ve 10 D)(d:x<10)(h:inIB I x=true):F x∈Ve 10 D:=by rw[<-q];exact mF.2 ⟨mU _,iB d h⟩
lemma sfB(s:Bool)(p:Slot):Vb s (Vg p)=Vb (!s) p:=by rcases p with ⟨g,b⟩;cases s<;>cases b<;>rfl
lemma sf1(s:Bool)(p:Slot):(Vb s p).1=p.1:=by cases s<;>rfl
def pinL(I x:Nat):LN:=Vm I x++(Vl I x).take 1
lemma pinLq I {x}(hx:x<10)(e:Es):V6 I e (F x)=(pinL I x).map λ y=>V7 e (F x) (F y):=by dsimp only[V6,pinL];rw[List.map_append,<-iNq I hx,List.map_map];congr 1;have q:=eNq I hx;cases h:Vl I x<;>rw[h] at q<;>rw[<-q]<;>rfl
lemma pLn{I x}(d:x<10)(e:Es):(V6 I e (F x)).length=(Vm I x).length+(if (Vl I x).isEmpty then 0 else 1):=by rw[pinLq I d,Vp,pinL,List.length_append];cases Vl I x<;>rfl
abbrev pR(D:Dag) (w:Ws) (e:Es) (x r y:Nat):=y<10/\adj (F x) (F y)/\V1 D (F x) r/\w (F x) r=V7 e (F x) (F y)
section Pin
variable {D:Dag} {k I x r:Nat} {w:Ws} {e:Es} {br:V->Nat} {o:Os k} (L:V0 D k I w e br o)
include L
lemma pAt(f:x<10)(h:inIB I x=false)(i:r<(pinL I x).length):pR D w e x r (pinL I x)[r]:=by have hp:r<(V6 I e (F x)).length:=by{rw[pinLq I f,Vp];exact i};have hn:=L.2.2.2.2.2.2.2.2.2.2 (F x) (by rw[nB f h];decide) r hp;have j:(pinL I x)[r]∈Vn x:=(List.mem_append.1 (List.getElem_mem i)).elim (λ d=>(lF.1 d).1) (λ d=>(lF.1 (List.mem_of_mem_take d)).1);have m:F (pinL I x)[r]∈(Vn x).map F:=Vo.2 ⟨_,j,rfl⟩;have h3:=nMap (F x);simp only[Fin.val_ofNat,mo f] at h3;rw[h3,lF] at m;refine⟨nMem f _ j,m.2,hn.1,hn.2.trans ?_⟩;simp only[pinLq I f,List.getElem_map]
lemma pIn(h:x<10)(d:inIB I x=false)(f:r<(Vm I x).length):pR D w e x r ((Vm I x).getD r 0):=by have hl:r<(pinL I x).length:=by{unfold pinL;simp;omega};have i:(Vm I x).getD r 0=(pinL I x)[r]:=by{rw[List.getD_eq_getElem _ _ f];simp[pinL,List.getElem_append_left f]};simpa only[i] using pAt L h d hl
lemma pEn(i:x<10)(f:inIB I x=false)(h:(Vl I x).isEmpty=false):pR D w e x (Vm I x).length ((Vl I x).getD 0 0):=by cases d:Vl I x with|nil=>{simp[d] at h}|cons y m=>{have hl:(Vm I x).length<(pinL I x).length:=by{unfold pinL;rw[d];simp};have j:(pinL I x)[(Vm I x).length]=y:=(by simp[pinL,d]);simpa only[j,List.getD_cons_zero] using pAt L i f hl}
end Pin
abbrev QT t d:=let v:=untriple t d;v.1<14/\v.2.1<10/\v.2.2<10/\¬adj (F v.2.1) (F v.2.2)
lemma qT{t d}(h:validTriple t d=true):QT t d:=by simp only[validTriple,sA,sD,sB,sC] at h;obtain⟨_,a,b,c,d⟩:=h;exact⟨a,b,c,λ q=>by rw[(aBi b c).2 q] at d;cases d⟩
lemma qC{t c d}(h:validCtx t c d=true):let u:=unctx c d;u.1<16/\u.2.1<14/\u.2.2<10/\QT t u.1:=by simp only[validCtx,sA,sD,sC] at h;exact⟨a4 _,h.2.2.1,h.2.2.2,qT h.2.1⟩
lemma qM{b a}(h:validMask b a=true):a<6/\(unmask b a).1<14/\(unmask b a).2.1.testBit (unmask b a).1=true:=by simp only[validMask,sA,sD,sC] at h;exact⟨h.2.1,h.2.2.1,h.2.2.2⟩
section Sound
variable {D:Dag} {k I P N:Nat} {w:Ws} {e:Es} {br:V->Nat} {o:Os k} {U X Y:LN} (H:Vd 10 D) (A:sem_Comp 10 adj D) (K:k<=3) (Q:mask I=Ve 10 D) (L:V0 D k I w e br o) (M:MOk D P) (S:SOk D e o N)
abbrev H0 D w e U X Y {k} (o:Os k):=Holds (trP D w e U X Y o)
lemma cN{x}(d:x<10){j}(f:j<cap k I (F x)):j<capN k I x:=by rw[cNq k I d];exact f
abbrev Lc(L:V0 D k I w e br o):=L.2.2.2.2.2.1
abbrev Li(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.1
abbrev Lw(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.1
abbrev Le(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.2.1
abbrev Lp(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.2.2
lemma zOpp2{z l a}(h:opp D w (F z) l (ep0 (J a))\/opp D w (F z) l (ep1 (J a)))(hz:z<10:=by first|assumption|omega)(hl:l<5:=by first|assumption|omega)(ha:a<14:=by first|assumption|omega):H0 D w e U X Y o [(fOpp z l (ep0N a),true),(fOpp z l (ep1N a),true)]:=jT λ n=>h.elim (λ j=>absurd ((v2 ⟨hz,hl,e0l ha⟩).2 (by rw[e0q ha];exact j)) n) (λ i=>R ((v2 ⟨hz,hl,e1l ha⟩).2 (by rw[e1q ha];exact i)))
lemma zF2{a x j b u v}{P0 R:Prop}(ha:EP.eP D w e U X Y o a <->P0/\¬opp D w (F x) j (F u)/\¬opp D w (F x) j (F v)/\R)(hx:x<10:=by first|assumption|omega)(hj:j<5:=by first|assumption|omega)(hu:u<10:=by first|assumption|omega)(hv:v<10:=by first|assumption|omega):H0 D w e U X Y o [(a,false),(fOpp x j (if b=1 then v else u),false)]:=Z λ hf ho=>(Classical.em (b=1)).elim (λ d=>(ha.1 hf).2.2.1 (T v2 (by simpa only[d,sT] using ho))) (λ d=>(ha.1 hf).2.1 (T v2 (by simpa only[d,sF] using ho)))
variable {g r:Nat}
include H A K Q L M S
omit M S in lemma z0 (_:g<16)(q:enabled0 k I g r=true):H0 D w e U X Y o (expand0 k I g r):=by interval_cases g<;>(simp only[expand0,enabled0,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{exact R (W v0 (live0_of H.1 A (F _)))};{have:=c5 q.2;exact cb v0 v1 (selfLab_of L)};{have:=c5 q.2;exact cb v0 v0 Nat.lt_of_succ_lt};{have:=c5 q.2.1;exact j3 λ _ d=>W v4 (labCommon_of L (T v1 d))};{apply G;intro i;have d:=(p3c K q.2.2.2.1).trans q.2.2.2.2;have ⟨t,h,f⟩:=sizeCode_of H A L (F _) _ _ d (T v0 i);exact jM K q.1 ⟨t,(mF.1 h).2,f⟩};{exact j0 λ d=>ineligNoRes_of L Q (iB q.1 q.2.1) (T v3 d)};{have ⟨n,h,i⟩:=q;rw[Bool.or_eq_true] at i;exact j0 λ d=>by{have f:=T v4 d;rcases i with m|j;{exact commonInelig H.1 A (mIn Q (by omega) m) (f0n (by omega) h (by omega)) f};{exact commonInelig H.1 A (mIn Q h j) (@f0n sctx ((r>>>4)&&&15) (r&&&15) h (by omega) (by omega)) (by have ⟨z,a,b⟩:=f;exact⟨z,b,a⟩)}}};{exact c3 v3 v3 v4 resCommon_of};{exact cb v5 v3 And.left};{exact cz v5 v3 And.right};{exact R (W v4 (adjCommon_of H A (mIn Q q.1 q.2.1) ((aBi q.1 q.2.2.1).1 q.2.2.2.2.2.1) ((aBi q.1 q.2.2.2.1).1 q.2.2.2.2.2.2)))};{have:=c5 q.2.2.2.2.2;apply jFFT;intro d m j;apply jT;intro i;rcases riSlots_of H A L Q (f0n q.1 q.2.2.1 q.2.2.2.1.symm) (nB q.1 q.2.1) q.2.2.2.2.1 (T v0 m) (T v4 d) with p|n|⟨t,h,f⟩;{exact absurd (W v1 p) j};{exact absurd (W v1 n) i};{exact jG ⟨t.1,t.2,W v5 ⟨h,f⟩⟩}};{have ⟨j,i,h,d⟩:=expose_of H A L (F _) (Vj ((r>>>4)&&&15)) (aMi q.2.1) (aMn q.1 q.2.1 q.2.2.2);have f:=cN q.1 i;exact jG ⟨j,f,(y4 ⟨q.1,q.2.1,(c5 f)⟩).2 ⟨h,d⟩⟩};{have:=c5 q.2.1;exact cb y4 v0 And.left};{have:=c5 q.2.1;exact Z λ f d=>(T y4 f).2 (F _) (mF.2 ⟨mU _,by rw[f0v q.2.2.2.1];exact q.2.2.2.2⟩) (T v1 d)};{exact cb v3 v3 (lex_step_bit L q (F 9) (λ y d=>by have:=y.2;simp at d;omega))}
omit M S in lemma z1 (_:16<=g)(_:g<32)(q:enabled0 k I g r=true):H0 D w e U X Y o (expand0 k I g r):=by interval_cases g<;>(simp only[expand0,enabled0,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{exact jQ λ d=>W v6 λ v h=>by{have f:v=F 9:=Fin.ext (by have:=v.2;simp;omega);rw[f];exact (v3).symm.trans (d.trans (v3 ⟨(by omega),(by omega)⟩))}};{exact j3 λ d h=>W v3 (lex_step_bit L q.1 (F _) (λ y f=>T v6 d y (by rw[f0v (by omega)] at f;omega)) (T v3 h))};{apply G;intro i;exact jQ λ d=>W v6 λ v j=>by{by_cases h:v.1=((r>>>3)&&&15);{have f:v=F ((r>>>3)&&&15):=Fin.ext (by rw[f0v (by omega)];exact h);rw[f];exact (v3).symm.trans (d.trans (v3 ⟨(by omega),(by omega)⟩))};{exact T v6 i v (by omega)}}};{exact j0 λ d=>hmInelig H A (mIn Q q.1 q.2) (T v7 d)};{exact cz v7 v0 (hmTop_of H A L (F _))};{apply jFF;intro i j;have d:=(p3c K q.2.2.2.1).trans q.2.2.2.2;have ⟨t,h,f⟩:=hmCode_of H A L (F _) _ _ d (T v7 i) (T v0 j);exact jM K q.1 ⟨t,(mF.1 h).2,f⟩};{have:=c5 q.2.2.2;exact cb v8 v0 And.left};{have:=c5 q.2.2.2.1;exact j3 λ f d=>W v1 ((T v8 f).2 (F _) (T v3 d))};{apply jFT;intro d m;have ⟨j,p,f,i⟩:=rsubTwo_of H A L (T v3 d) (λ n=>m (W v7 n)) (unsl ((r>>>3)&&&63)).2;have h:=cN q.2.1 p;exact⟨(fRsub (r&&&7) (unsl ((r>>>3)&&&63)).1 j,true),Vo.2 ⟨j,lF.2 ⟨lR.2 h,by simp[f]⟩,rfl⟩,bt.2 ((v8 ⟨(by omega),q.2.1,(c5 h)⟩).2 i)⟩};{have:=c5 q.2;exact j0 λ d=>oppSelf_of H.1 L (F _) _ (T v2 d)};{have:=c5 q.2.1;exact G λ _=>j3 λ f d=>W v7 (labOppMerge_of H.1 L (T v1 f) (T v2 d))};{have u:=c5 q.2.1;apply jFFT;intro j f h;have ⟨l,p,i,m⟩:=smateAny_of H.1 L (T v1 f) (λ n=>h (W v2 n));have d:=cN q.2.2.1 p;exact jG ⟨l,d,(y9 ⟨q.1,u,q.2.2.1,(c5 d)⟩).2 ⟨T v0 j,i,m⟩⟩};{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2;exact B λ d=>W v0 (T y9 d).2.1};{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact jI λ j=>by{have ⟨f,h,d⟩:=T y9 j;by_cases i:((r>>>16)&&&1)=1;{simp only[i,sT];refine (v2).trans (Iff.trans ?_ (v2).symm);simp only[opp,f,h,d,true_and]};{simp only[i,sF];refine (v1).trans (Iff.trans ?_ (v1).symm);simp only[lab,f,h,d,true_and]}}};{have u:=c5 q.2.1;apply jFFT;intro j d h;have ⟨l,p,i,n⟩:=omateAny_of H.1 L (T v2 d) (λ m=>h (W v1 m));have f:=cN q.2.2.1 p;exact jG ⟨l,f,(x0 ⟨q.1,u,q.2.2.1,(c5 f)⟩).2 ⟨T v0 j,i,n⟩⟩};{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2;exact B λ d=>W v0 (T x0 d).2.1}
omit S in lemma z2 (_:32<=g)(_:g<48)(q:enabled1 k I P g r=true):H0 D w e U X Y o (expand1 k I g r):=by have hE:=Le L;interval_cases g<;>(simp only[expand1,enabled1,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact jI λ j=>by{have ⟨f,h,d⟩:=T x0 j;by_cases i:((r>>>16)&&&1)=1;{simp only[i,sT];refine (v2).trans (Iff.trans ?_ (v1).symm);simp only[lab,opp,f,h,d,Vh,true_and]};{simp only[i,sF];refine (v1).trans (Iff.trans ?_ (v2).symm);simp only[lab,opp,f,h,d,true_and]}}};{have:=c5 q.2.1;exact k3 λ _ d f=>ineligOppNF_of H A L Q (f0n q.1 q.2.2.1 q.2.2.2.1.symm) (iB q.2.2.1 q.2.2.2.2) (T v2 d) (T u1 f)};{have ⟨v,u,f,_,p,n,m⟩:=q;have:=c5 u;exact k3 λ _ h j=>by{have i:=sem_inelig_pure graph_ok H.1 A (mIn Q f p) (T v2 h).2;have d:=(T v2 j).2;rw[i,Finset.mem_singleton] at d;exact f0n n f m d}};{have:=c5 q.2.1;apply G;intro h;exact jI λ f=>by{have j:=V3 H A L Q (f0n q.1 q.2.2.1 q.2.2.2.1.symm) (iB q.2.2.1 q.2.2.2.2.1) (T v2 f);have d:=congrArg Vg j.symm;rw[Vh] at d;have i:=live0_of H.1 A (F ((r>>>6)&&&15));refine (v1).trans (Iff.trans ?_ (v2).symm);simp only[lab,opp,T v0 h,i,d,true_and]}};{have ⟨h1,h2,h,z,h5,h6⟩:=q;have:=c5 h6;have f:(r&&&15)≠((r>>>4)&&&15):=λ p=>by{rw[p,z] at h2;exact Bool.noConfusion h2};apply jFF;intro n m;exact Z λ j i=>by{have v:=V3 H A L Q (f0n h1 h f) (iB h z) (T v2 j);have u:=V3 H A L Q (f0n h1 h f) (iB h z) (T v2 i);have d:=congrArg Vg (v.trans u.symm);rw[Vh,Vh] at d;have a0:=Li L (F (r&&&15)) _ _ (T v0 n) (T v0 m) d;omega}};{exact R (W v2 ⟨live0_of H.1 A (F _),(inelig_unique_slot H A L Q (iB q.1 q.2.1)).2 (F _) ((aBi q.1 q.2.2.1).1 q.2.2.2)⟩)};{have ⟨h1,n,h3,h4,_,h6,h3lt,h7⟩:=q;have a3:Bzero 10 D=0:=by{rw[h1] at M;exact M};have ⟨f,d,i⟩:=nLt n h3lt h7;have v:¬adj (F (r&&&15)) (F ((r>>>4)&&&15)):=λ ha=>by{rw[(aBi n h4).2 ha] at h6;exact Bool.noConfusion h6};apply G;intro h;have ⟨l,hl,a2,z,u,m⟩:=ineligFilter_of H A a3 L Q (iB n h3) v d (T v2 h);have j:=cN f hl;have a0:=(eSq n f d).2.2.1;exact jG ⟨l,j,(x1 ⟨n,h4,i,(c5 j)⟩).2 ⟨by rw[a0];exact a2,z,u,λ x2 p=>(m x2 p).1⟩⟩};{exact j0 λ d=>ineligOppInelig_of H A L Q (iB q.1 q.2.1) (iB q.2.2.1 q.2.2.2.1) (f0n q.1 q.2.2.1 q.2.2.2.2) (T v2 d)};{have f:((r>>>4)&&&1)<2:=a1 _;exact j0 λ d=>by{have h:=(v9 ⟨f,q,(enl q)⟩).1 d;rw[enq (by omega) q,bnot1 f] at h;exact (hE _ (J _)).2 h}};{exact j3 λ f d=>W v7 (by{have ⟨j,i,h⟩:=Lw L (ep0 (J (r&&&15))) (e (J (r&&&15))) (by simpa[endpoint,Vb] using (hE false (J (r&&&15))).1);exact labOppMerge_of H.1 L ⟨i,by rw[h];simpa[es,Vb] using T v9 f⟩ ⟨i,by rw[h];simpa[es,Vb,Vg] using T v9 d⟩})};{have d:((r>>>4)&&&1)<2:=a1 _;exact R ((v9 ⟨d,q,(enl q)⟩).2 (by rw[enq d q];exact (Vi.1 (hE _ (J _)).1).2.1))};{let b0:=(r&&&1)==1;let z:=J ((r>>>1)&&&15);let x0:=F ((r>>>5)&&&15);let p0:=Vb b0 (e z);have hs:(r&&&1)<2:=a1 _;apply jFT;intro v u;have f:=(hE b0 z).1;have i:=(Vi.1 f).1;have h:x0∉supp 10 D (10+p0.1):=λ n=>u (W v9 (by rw[bnot1 hs];have d:=sem_supp_and_sub H.1 i (sem_W_and H.1 f) (!p0.2) n;rw[show (p0.1,!p0.2)=Vb (!b0) (e z) by rw[Vc];rfl] at d;exact d));have ⟨j,hj,p⟩:=Lw L x0 _ (Vi.2 ⟨i,T v9 v,h⟩);have m:=cN q.2 (lt_of_lt_of_le hj (Lc L _));exact jG ⟨j,m,(u0 ⟨hs,q.1,q.2,(c5 m)⟩).2 ⟨hj,p⟩⟩};{have:(r&&&1)<2:=a1 _;have:=c5 q.2.2.2;exact Z λ f d=>by{have ⟨i,m⟩:=T u0 f;have ⟨h,j⟩:=T u0 d;have:=Li L (F _) _ _ i h (m.trans j.symm);omega}};{have:(r&&&1)<2:=a1 _;have:=c5 q.2.2;exact cb u0 v0 And.left};{have:(r&&&1)<2:=a1 _;have:=c5 q.2.2;exact B λ d=>W v9 (by rw[es,<-(T u0 d).2];exact (Vi.1 (L.2.2.2.2.2.2.1 _ _)).2.1)};{have j:(r&&&1)<2:=a1 _;have:=c5 q.2.2;exact Z λ m f=>by{have ⟨d,h⟩:=T u0 m;have i:=T v9 f;rw[bnot1 j,es,Vc,<-h] at i;exact oppSelf_of H.1 L (F _) _ ⟨d,i⟩}}
omit H A Q M S in lemma z3 (_:48<=g)(_:g<64)(q:enabled1 k I P g r=true):H0 D w e U X Y o (expand1 k I g r):=by have hE:=Le L;interval_cases g<;>(simp only[expand1,enabled1,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have i:(r&&&1)<2:=a1 _;have:=c5 q.2.2.1;exact jI λ j=>by{have ⟨d,f⟩:=T u0 j;by_cases h:((r>>>15)&&&1)=1;{simp only[h,sT];refine (v2).trans (Iff.trans ?_ (v9).symm);simp only[opp,es,d,f,<-Vc,<-bnot1 i,true_and]};{simp only[h,sF];refine (v1).trans (Iff.trans ?_ (v9).symm);simp only[lab,es,d,f,true_and]}}};{have:=c5 q.2.2.2;have d:(unsl (r&&&63)).2<(V6 I e (F (unsl (r&&&63)).1)).length:=by{rw[pLn q.1];exact q.2.2.1};exact R (W v0 (Lp L (F _) (by rw[nB q.1 q.2.1];decide) _ d).1)};{have:=c5 q.2.2.2.1;have ⟨h,d,i,j⟩:=pIn L q.1 q.2.1 q.2.2.1;have f:(Vm I (unsl (r&&&63)).1).getD (unsl (r&&&63)).2 0=((r>>>6)&&&15):=(List.getD_eq_getElem _ 0 q.2.2.1).trans ((List.getD_eq_getElem _ 10 q.2.2.1).symm.trans q.2.2.2.2);rw[f] at h d j;exact R (W v2 ⟨i,by rw[j];exact (Vi.1 (pinTarget_mem_W hE d).2).2.1⟩)};{have:=c5 q.2.2.2;have ⟨d,f,h,m⟩:=pIn L q.1 q.2.1 q.2.2.1;have ⟨p,n,j,i⟩:=eSq q.1 d f;exact R (W u0 ⟨h,by rw[m,V7,j,i]⟩)};{have:=c5 q.2.2.2;have ⟨d,f,h,m⟩:=pEn L q.1 q.2.1 q.2.2.1;have ⟨p,n,j,i⟩:=eSq q.1 d f;exact R (W u0 ⟨h,by rw[m,V7,j,i]⟩)};{have:((r>>>12)&&&1)<2:=a1 _;have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact j3 λ j i=>by{have ⟨f,_,h⟩:=T y9 j;have ⟨_,d⟩:=T u0 i;exact W u0 ⟨f,h.symm.trans d⟩}};{have j:((r>>>12)&&&1)<2:=a1 _;have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact j3 λ n m=>by{have ⟨h,_,i⟩:=T x0 n;have ⟨_,f⟩:=T u0 m;have d:=congrArg Vg (i.symm.trans f);rw[Vh] at d;exact W u0 ⟨h,by rw[bnot1 j,Vc];exact d⟩}};{have:=c5 q.2;exact cb u1 v0 And.left};{have:((r>>>6)&&&1)<2:=a1 _;have:=c5 q.2.1;exact Z λ f d=>(T u1 f).2 (J _) _ (T u0 d).2};{have:=c5 q.2;exact cb u2 v0 And.left};{have:=c5 q.2.1;exact Z λ h f=>by have d:=(T v2 f).2;rw[(T u2 h).2] at d;exact Finset.notMem_empty _ d};{exact cb u3 u5 (congrArg Prod.fst)};{exact B λ d=>W u5 (by unfold sgate;rw[T u4 d];rfl)};{apply jFT;intro d f;rcases sem_same_gate (T u5 d).symm with i|h;{exact absurd (W u3 i) f};{exact R (W u4 h)}};{have:((r>>>14)&&&1)<2:=a1 _;have:((r>>>15)&&&1)<2:=a1 _;have:=c5 q.2.2.2;exact j3 λ j i=>by{have d:=(T u0 j).2.symm.trans (T u0 i).2;have h:((r>>>14)&&&1)=0\/((r>>>14)&&&1)=1:=(by omega);have f:((r>>>15)&&&1)=0\/((r>>>15)&&&1)=1:=(by omega);rcases h with h|h<;>rcases f with f|f<;>simp only[h,f] at d ⊢;{exact W u3 (sflip_inj false d)};{exact W u4 (by simpa[Vb,Vg] using d)};{exact W u4 (by change Vb true _=Vb false _ at d;rw[sflip_true,sflip_false] at d;have h'':=congrArg Vg d;rwa [Vh] at h'')};{exact W u3 (sflip_inj true d)}}};{have:((r>>>8)&&&1)<2:=a1 _;exact jI λ d=>(v9).trans (by unfold es;rw[T u3 d];exact (v9).symm)}
omit H A Q L M S in lemma z4 (_:64<=g)(_:g<80)(q:enabled2 k I P g r=true):H0 D w e U X Y o (expand2 k I P g r):=by interval_cases g<;>(simp only[expand2,enabled2,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have d:((r>>>8)&&&1)<2:=a1 _;exact jI λ f=>(v9).trans (by{unfold es;rw[T u4 f,sfB,<-bnot1 d];exact (v9).symm})};{exact Z λ d f=>by have a:=T u5 d;have b:=T u6 f;unfold sgate at a;unfold V4 at b;omega};{apply jTT;intro d f;have a:(e (J _)).1≠(e (J _)).1:=λ i=>d (W u5 i);have b:¬(e (J _)).1<(e (J _)).1:=λ h=>f (W u6 h);exact R (W u6 (by unfold V4;omega))};{exact Z λ f d=>by have a:=T u6 f;have b:=T u6 d;unfold V4 at a b;omega};{exact c3 u6 u6 u6 Nat.lt_trans};{have:=c5 q.2.2;exact cb u7 v0 And.left};{have:((r>>>10)&&&1)<2:=a1 _;have:=c5 q.2.2;exact Z λ i f=>by have h:=(T u7 i).2;have d:=congrArg Prod.fst (T u0 f).2;rw[sf1] at d;omega};{have:((r>>>10)&&&1)<2:=a1 _;have:=c5 q.2.2.1;exact j3 λ i f=>W u6 (by have h:=(T u7 i).2;have d:=congrArg Prod.fst (T u0 f).2;rw[sf1] at d;unfold V4;omega)};{have:=c5 q.2.2;exact cb t0 u7 And.left};{have:=c5 q.2.2;exact cb t0 u1 And.right};{have:=c5 q.2.2;exact cb t1 u7 And.left};{have:=c5 q.2.2;exact cb t1 u2 And.right};{have d:=c5 q.2.1;have:=c5 q.2.2;exact B λ f=>(v0 ⟨(e0l q.1),d⟩).2 (by rw[e0q q.1];exact (T u9 f).1)};{have:=c5 q.2.1;have d:=c5 q.2.2;exact B λ f=>(v0 ⟨(e1l q.1),d⟩).2 (by rw[e1q q.1];exact (T u9 f).2.1)};{have d:=c5 q.2.1;have:=c5 q.2.2;exact Z λ f h=>secNotRa0_of (T u9 f) (by rw[<-e0q q.1];exact (u0 ⟨(by omega),q.1,(e0l q.1),d⟩).1 h)};{have:=c5 q.2.1;have d:=c5 q.2.2;exact Z λ f h=>secNotRa1_of (T u9 f) (by rw[<-e1q q.1];exact (u0 ⟨(by omega),q.1,(e1l q.1),d⟩).1 h)}
omit Q S in lemma z5 (_:80<=g)(_:g<96)(q:enabled2 k I P g r=true):H0 D w e U X Y o (expand2 k I P g r):=by have hE:=Le L;interval_cases g<;>(simp only[expand2,enabled2,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have ⟨d,u,p,h⟩:=q;have j:=c5 u;have i:=c5 p;exact jI λ n=>by{have f:=secEq_of (T u9 n) (F ((r>>>9)&&&15));by_cases m:((r>>>13)&&&1)=1;{simp only[m,sT];exact (v1 ⟨(e1l d),i,h⟩).trans (by rw[e1q d,f.1,<-e0q d];exact (v2 ⟨(e0l d),j,h⟩).symm)};{simp only[m,sF];exact (v1 ⟨(e0l d),j,h⟩).trans (by rw[e0q d,f.2,<-e1q d];exact (v2 ⟨(e1l d),i,h⟩).symm)}}};{apply G;intro h;have ⟨j,p,i,n,m⟩:=hasSecAny_of H.1 L (T u8 h);have f:j<capN k I (ep0N (r&&&15)):=by{rw[cNq k I (e0l q),e0q q];exact p};have d:i<capN k I (ep1N (r&&&15)):=by{rw[cNq k I (e1l q),e1q q];exact n};exact⟨(fSecp (r&&&15) j i,true),List.mem_flatMap.2 ⟨j,lR.2 f,Vo.2 ⟨i,lR.2 d,rfl⟩⟩,bt.2 ((u9 ⟨q,(c5 f),(c5 d)⟩).2 m)⟩};{apply jT;intro f;rcases P with _|_|_|_;{omega};{rcases stepAny0_of H A M hE (J _) with d|⟨z,h⟩;{exact absurd (W t2 d) f};{exact jG ⟨z.1,z.2,W t4 (by rw[f0e];exact h)⟩}};{exact M.elim};{exact M.elim}};{contradiction};{exact c3 u5 t2 t2 sameStay_of};{exact c3 u5 t4 t4 samePick_of};{have:=c5 q.2.2.2;exact cb t5 u7 And.left};{have:=c5 q.2.2.2;exact G λ d=>zOpp2 (T t5 d).2};{apply jFT;intro j f;have ⟨l,m,h⟩:=pickZH0_of H A L (T t4 j) (λ i=>f (W u8 i));have d:=cN q.2.2 m;exact jG ⟨l,d,(t5 ⟨q.2.1,q.2.2,(c5 d)⟩).2 h⟩};{contradiction};{contradiction};{have:=c5 q.2.1;exact cb v2 v0 And.left};{contradiction};{contradiction};{contradiction};{contradiction}
omit Q M S in lemma z6 (_:96<=g)(_:g<101)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by have hE:=Le L;have:=a4 r;interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{contradiction};{have ⟨j,n,m,i⟩:=qT q.2;exact j3 λ h f=>W y2 (bcInit_of H A hE i (by{by_cases d:((r>>>4)&&&1)=1;{simp only[d,sT] at h f;exact Or.inr ⟨T (v9 (s:=0)) h,T (v9 (s:=1)) f⟩};{simp only[d,sF] at h f;exact Or.inl ⟨T (v9 (s:=0)) h,T (v9 (s:=1)) f⟩}}))};{have ⟨n,_,_,m⟩:=qT q.2.1;apply jFFT;intro p i j;rcases bcStay_of H A L m (T y2 p) (T t2 i) with hs|⟨z,h,f,d,l,v,u⟩;{exact absurd (W u8 hs) j};{exact jU n ⟨z,h,f,d,l,v,(t1 ⟨q.2.2,z.2,(c5V v)⟩).2 (by rw[f0e];exact u)⟩}};{contradiction};{contradiction}
omit Q M S in lemma z7 (_:101<=g)(_:g<108)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by have:=a6 r;interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have ⟨b8,h,j,a9,_,_,a3⟩:=qC q.2;apply jFF;intro b6 a2;rcases bcPick_of H A L a3 (T y2 b6) (T t4 a2) with hs|⟨z,a0,v,u,l,p,b7⟩|⟨b5,b4,a7⟩|⟨l,p,a8⟩|⟨n,a5,f⟩;{exact jL (jL (jL (jR (R (W u8 hs)))))};{exact jL (jL (jL (jL (jU a9 ⟨z,a0,v,u,l,p,(t1 ⟨h,z.2,(c5V p)⟩).2 (by rw[f0e];exact b7)⟩))))};{apply jL;apply jL;apply jR;split_ifs with i;{exact R (W v7 a7)};{exact absurd ⟨λ m=>b5 (by rw[m]),λ m=>b4 (by rw[m])⟩ i}};{have d:=cN j p;have:=c5 d;exact jL (jR (jF2 ⟨l,d,a8.imp (y5 ⟨(a6 r),(c5 d)⟩).2 (t0 ⟨h,j,(c5 d)⟩).2⟩))};{have hne':n.1≠(unctx X (r&&&63)).2.1:=λ m=>a5 (by rw[<-f4e n,m]);exact jR ⟨(fEse (r&&&63) n.1,true),Vo.2 ⟨n.1,lF.2 ⟨lR.2 n.2,by simp[hne']⟩,rfl⟩,bt.2 (W y6 (by rw[f4e];exact f))⟩}};{have ⟨_,d,f,_,_,_,_⟩:=qC q.2.1;have:=c5 q.2.2;exact cb y5 u7 And.left};{have ⟨_,_,d,_,h,f,_⟩:=qC q.2.1;have:=c5 q.2.2;exact zF2 y5};{have ⟨_,_,h,f,_,_,_⟩:=qC q.2.1;have:=c5 q.2.2;exact G λ d=>zOpp2 (T y5 d).2.2.2};{have ⟨_,d,_,_,_,_,_⟩:=qC q.2.1;exact cb y6 u6 And.left};{have ⟨_,_,i,_,_,_,_⟩:=qC q.2.1;apply jFT;intro h j;rcases (T y6 h).2.1 with f|d;{exact absurd (W (v9 (s:=0)) f) j};{exact R (W (v9 (s:=1)) d)}};{have d:=(qC q.2.1).1;exact B λ f=>W y2 (T y6 f).2.2}
omit Q S in lemma z8 (_:108<=g)(_:g<115)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢);{have ⟨hm1,hvm⟩:=q;subst hm1;have ⟨ha6,hd14,hdbit⟩:=qM hvm;by_contra hnh;have hns:¬has_sec D e (J (unmask Y (r&&&7)).1):=λ hs=>hnh ⟨_,List.mem_cons_self ..,bt.2 (W (u8 hd14) hs)⟩;have hstay:∀e0:Ei,(unmask Y (r&&&7)).2.1.testBit e0.1=true->¬stay_empty D (10+(e e0).1):=λ e0 he0 hs=>hnh ⟨(fStay e0.1,true),List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨e0.1,lF.2 ⟨lR.2 e0.2,he0⟩,List.mem_cons_self ..⟩)),bt.2 (W (t2 e0.2) (by rwa[f4e]))⟩;have hpick:∀e0:Ei,(unmask Y (r&&&7)).2.1.testBit e0.1=true->∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=false->¬pick_z D (10+(e e0).1) z:=λ e0 he0 z hz hp=>hnh ⟨(fPick e0.1 z.1,true),List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨e0.1,lF.2 ⟨lR.2 e0.2,he0⟩,List.mem_cons_of_mem _ (Vo.2 ⟨z.1,lF.2 ⟨lR.2 z.2,by simp[hz]⟩,rfl⟩)⟩)),bt.2 (W (t4 ⟨e0.2,z.2⟩) (by rwa[f4e,f0e]))⟩;have hfree:∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=true->∀l<cap k I z,¬free_slot D w e z l:=λ z hz l hl hf=>by{have hlN:l<capN k I z.1:=cN z.2 (by rwa[f0e]);exact hnh ⟨(fFree z.1 l,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_self ..⟩⟩)),bt.2 (W (u1 ⟨z.2,c5 hlN⟩) (by rwa[f0e]))⟩};have hopp:∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=true->∀l<cap k I z,∀y:V,(unmask Y (r&&&7)).2.2.testBit y.1=true->¬opp D w z l y:=λ z hz l hl y hy ho=>by{have hlN:l<capN k I z.1:=cN z.2 (by rwa[f0e]);exact hnh ⟨(fOpp z.1 l y.1,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (Vo.2 ⟨y.1,lF.2 ⟨lR.2 y.2,hy⟩,rfl⟩))⟩⟩)),bt.2 (W (v2 ⟨z.2,c5 hlN,y.2⟩) (by rwa[f0e,f0e]))⟩};have hesc:∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=true->∀l<cap k I z,¬mescProp D w e (J (unmask Y (r&&&7)).1) (unmask Y (r&&&7)).2.1 z l:=λ z hz l hl hm=>by{have hlN:l<capN k I z.1:=cN z.2 (by rwa[f0e]);exact hnh ⟨(fMesc (r&&&7) z.1 l,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩)),bt.2 (W (y7 ⟨ha6,z.2,c5 hlN⟩) (by rwa[f0e]))⟩};exact maskClosure_of H A M L (by rwa[Fin.val_ofNat,mo hd14]) hns hstay hpick hfree hopp hesc};{have ⟨_,hvm,hz,hl⟩:=q;have ⟨ha6,hd14,_⟩:=qM hvm;have:=c5 hl;exact G λ hm=>zOpp2 (T (y7 ⟨ha6,hz,this⟩) hm).1 hz this hd14};{have ⟨_,hvm,hz,hl⟩:=q;have ⟨ha6,_,_⟩:=qM hvm;have hl5:=c5 hl;apply G;intro hm;obtain⟨_,e',he',s,hra⟩:=T (y7 ⟨ha6,hz,hl5⟩) hm;cases s;{exact⟨(fRa 0 e'.1 (unsl ((r>>>3)&&&63)).1 (unsl ((r>>>3)&&&63)).2,true),List.mem_flatMap.2 ⟨e'.1,lF.2 ⟨lR.2 e'.2,he'⟩,by simp⟩,bt.2 (W (u0 ⟨by omega,e'.2,hz,hl5⟩) (by simpa[f4e] using hra))⟩};{exact⟨(fRa 1 e'.1 (unsl ((r>>>3)&&&63)).1 (unsl ((r>>>3)&&&63)).2,true),List.mem_flatMap.2 ⟨e'.1,lF.2 ⟨lR.2 e'.2,he'⟩,by simp⟩,bt.2 (W (u0 ⟨by omega,e'.2,hz,hl5⟩) (by simpa[f4e] using hra))⟩}};{contradiction};{contradiction};{contradiction};{contradiction}
omit H A K Q L M S in lemma z9 (_:115<=g)(_:g<117)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by interval_cases g<;>simp[enabled3] at q
omit Q M S in lemma za (_:117<=g)(_:g<128)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have ⟨d,f,i⟩:=nLt q.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1;have h:=c5 q.2.2.2.2.2.2.2.2;exact B λ j=>(t1 ⟨(eSq q.2.1 d f).1,d,h⟩).2 (T x1 j).1};{have ⟨d,_,f⟩:=nLt q.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1;have:=c5 q.2.2.2.2.2.2.2.2;exact B λ h=>W u1 (T x1 h).2.1};{have ⟨d,_,h⟩:=nLt q.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1;have:=c5 q.2.2.2.2.2.2.2.2;exact Z λ i f=>(T x1 i).2.2.1 (T v1 f)};{have ⟨_,m,_,u,_,_,i3,i,n,f,d⟩:=q;have ⟨h,_,j⟩:=nLt m i3 i;have:=c5 n;exact B λ p=>W v1 ((T x1 p).2.2.2 (F _) ((aBi m f).1 d))};{contradiction};{exact Z λ f d=>f0n (by omega) q.2.2.2 (by omega) (pickUniq_of H.1 (T t4 f) (T t4 d))};{contradiction};{contradiction};{have:=c5 q.2.1;exact cb v1 v0 labLive_of};{apply G;intro i;rcases commonExit_of H A L (T v4 i) with ⟨j,n,d⟩|⟨l,m,d⟩;{have h:=cN (by omega) n;exact jL (jG ⟨j,h,(v1 ⟨(by omega),(c5 h),q.2.1⟩).2 d⟩)};{have f:=cN q.2.1 m;exact jR (jG ⟨l,f,(v1 ⟨q.2.1,(c5 f),(by omega)⟩).2 d⟩)}};{have ⟨hx,hni,hp,hy1,hy2,hjc⟩:=q;have hj5:=c5 hjc;have ht1:(if ((r>>>4)&&&3)=2 then 1 else 0)<3:=(by split_ifs<;>omega);have ht2:(if ((r>>>4)&&&3)=0 then 1 else 2)<3:=(by split_ifs<;>omega);exact jT λ hm=>G λ c1=>G λ c2=>G λ h1=>jT λ hn2=>G λ h2=>jT λ hn1=>G λ hj=>jT λ hr1=>jT λ hr2=>by{have h5:=rsubDisj_of H A L (T v3 c1) (T v3 c2) (T v3 h1) (λ u=>hn2 (W v3 u)) (T v3 h2) (λ u=>hn1 (W v3 u)) (λ u=>hm (W v7 u)) (T v0 hj) (λ u=>hr1 (W v8 u)) (λ u=>hr2 (W v8 u));split_ifs with hk;{exact R (W v0 (by show 4<fF D (F (r&&&15));omega))};{have hc:=L.2.2.2.2.2.1 (F (r&&&15));unfold cap at hc;rw[f0v hx] at hc;dsimp only[R1.B,inIB] at hni;rw[hni] at hc;simp only[Bool.false_eq_true,ite_false] at hc;omega}}}
omit S in lemma zS(c:Nat)(q:enS k I P N U X Y c=true):H0 D w e U X Y o (expS k I P U X Y c):=by unfold expS expandScheme;unfold enS enabled at q;dsimp only at q ⊢;have d:c&&&127<128:=aM 7 c;generalize c&&&127=g at d q ⊢;split_ifs at q ⊢ with a b e;{exact if f:g<16 then z0 H A K Q L f q else z1 H A K Q L (by omega) b q};{exact if f:g<48 then z2 H A K Q L M (by omega) f q else z3 K L (by omega) a q};{exact if f:g<80 then z4 K (by omega) f q else z5 H A K L M (by omega) e q};{exact if f:g<101 then z6 H A K L (by omega) f q else if f:g<108 then z7 H A K L (by omega) f q else if f:g<115 then z8 H A K L M (by omega) f q else if f:g<117 then z9 (by omega) f q else za H A K L (by omega) d q}
end Sound
section K
variable {D:Dag} {k I mode sym:Nat} {b:V->Nat} {e:Es}
abbrev Gk D k I m b e:=Vd 10 D/\sem_Comp 10 adj D/\k<=3/\mask I=Ve 10 D/\PureBranch 10 D b/\(Vf 10 D b).card<=k/\GoodEdge D e/\MOk D m
lemma kC(p:CK k I mode sym)(g:Gk D k I mode b e)(_j:∀w o,V0 D k I w e b o->SOk D e o sym):False:=by obtain⟨h,d,f,q,i,m,v,n⟩:=g;obtain⟨w,o,L⟩:=construct_layout_from h d q i m v;obtain⟨t,c,x,u⟩:=p;exact u (trP D w e t c x o) (zS h d f q L n)
abbrev k0(hK:CK k I mode 0) (g:Gk D k I mode b e):=kC hK g λ _ _ _=>trivial
end K
end P3
open DagTools

end PriorG11.SharedCases
namespace PriorG11.SharedCases
open DagTools
def impossibleCell [Slice] (b : CellData) : Prop := ∀ v : Nat → Bool,
  (∀ key, Rup.enS b.budget b.independentMask b.mode b.symmetry b.pins b.pairs b.masks key=true →
    Rup.Holds v (Rup.expS b.budget b.independentMask b.mode b.pins b.pairs b.masks key)) → False

def provedCells [Slice] (cells : List CellData) := ∀ c ∈ cells, impossibleCell c

def permits (I R B : Nat) (c : CellData) : Bool := decide
  (c.independentMask=I ∧ c.budget≤3 ∧ R≤c.budget ∧ c.symmetry=0 ∧ (c.mode=0 ∨ c.mode=1 ∧ B=0))

def finiteDispatch [Slice] (cells : List CellData) : Bool := orbitMasks.all fun I =>
  let count := (mask I).card
  decide (count≤4) && (List.range 4).all fun R => (List.range 4).all fun B =>
    if R+B+1 ≤ count then cells.any (permits I R B) || (List.finRange 10).any fun x =>
      decide (I.testBit x.val=false ∧ 2+R < b4 I x)
    else true

open P3 in
theorem lowerFromAbelianTarskiArtSabintsev [Slice] (cells : List CellData) (all : provedCells cells) (table : finiteDispatch cells=true) :¬(∃C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C/\C.size<=18/\(∀x:Fin 10->Bool,(C.eval (List.ofFn x)=true <->∃u v:Fin 10,(u.1,v.1)∈k7/\x u=true/\x v=true))):=by
  rintro⟨C,hM,h7,h3⟩
  obtain⟨D0,d,h1,i⟩:=normalized C hM h3
  have p:=le_trans h1 h7
  obtain⟨b0,h5⟩:=sem_exists_pureBranch graph_ok d.1 i
  have h8:=surplus_bound d p b0 h5
  obtain⟨m,hm⟩:=repr_finset (ineligSet 10 D0)
  have h4:m.1≠0:=λ h0=>by{have e:(ineligSet 10 D0).card=0:=(by rw[<- hm,h0];decide +kernel);omega}
  obtain⟨a,z⟩:=orbit_dispatch m h4 (by rw[hm];exact inelig_indep d i)
  let σ:=autPerm a
  let D:=relabel σ D0
  let b:=relabelBranch σ b0
  have h:StrictLive 10 D:=relabel_strictLive σ d
  have hc:sem_Comp 10 adj D:=rename d i σ (auto_autPerm a)
  have hb:PureBranch 10 D b:=relabel_pureBranch σ d.1 h5
  have h6:(residualUnits 10 D b).card+Bzero 10 D+1<=(ineligSet 10 D).card:=surplus_bound h (by rw[relabel_length];exact p) b hb
  obtain⟨e,hE⟩:=get_edges h.1 hc
  have j:mask (maskImage a m.1)=ineligSet 10 D:=(by rw[mask_maskImage a m,hm,relabel_ineligSet σ d.1])
  generalize maskImage a m.1=I at z j
  rw[<- j] at h6
  let R:=(residualUnits 10 D b).card
  let B := Bzero 10 D
  have entry := List.all_eq_true.mp table I z
  have both := (Bool.and_eq_true _ _).mp entry
  have bound : (mask I).card ≤ 4 := of_decide_eq_true both.1
  have fitting : R+B+1 ≤ (mask I).card := h6
  have hR : R ∈ List.range 4 := List.mem_range.mpr (by omega)
  have hB : B ∈ List.range 4 := List.mem_range.mpr (by omega)
  have dispatch := List.all_eq_true.mp (List.all_eq_true.mp both.2 R hR) B hB
  simp only [if_pos fitting,Bool.or_eq_true,List.any_eq_true] at dispatch
  rcases dispatch with ⟨c,member,permit⟩ | ⟨v,_,pin⟩
  · have requirements : c.independentMask=I ∧ c.budget≤3 ∧ R≤c.budget ∧ c.symmetry=0 ∧
        (c.mode=0 ∨ c.mode=1 ∧ B=0) := of_decide_eq_true permit
    obtain ⟨hmI,hk,hr,hs,mode⟩ := requirements
    have md : MOk D c.mode := by
      rcases mode with zero | ⟨one,hz⟩
      · rw [zero]; trivial
      · rw [one]; exact hz
    have killed : CK c.budget I c.mode 0 := by
      refine ⟨c.pins,c.pairs,c.masks,?_⟩
      have done := all c member
      unfold impossibleCell at done
      simpa only [hmI,hs] using done
    exact k0 killed ⟨h,hc,hk,j,hb,hr,hE,md⟩
  · have p : I.testBit v.val=false ∧ 2+R < b4 I v := of_decide_eq_true pin
    exact pin_kill h hc j hb (le_refl R) v p.1 p.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch0 : @finiteDispatch ⟨0⟩ cells0=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch1 : @finiteDispatch ⟨1⟩ cells1=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch2 : @finiteDispatch ⟨2⟩ cells2=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch3 : @finiteDispatch ⟨3⟩ cells3=true := by decide +kernel
end PriorG11.SharedCases

namespace PriorG11.Bounds
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def edges : List (Nat × Nat) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
abbrev G := PEqualNP.EdgeOwnership.edgeGraph 11 edges
theorem adjacent (a b : Fin 11) : G.Adj a b ↔ (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges := by
  exact (show ∀ a b : Fin 11, G.Adj a b ↔ (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges by decide +kernel) a b
open PriorG11.SharedCases

abbrev Certified := ∀ i : Fin 4, @provedCells ⟨i⟩ (cellsAt i)

theorem dispatchAt (i : Fin 4) : @finiteDispatch ⟨i⟩ (cellsAt i) = true := by
  fin_cases i
  · exact SharedCases.dispatch0
  · exact SharedCases.dispatch1
  · exact SharedCases.dispatch2
  · exact SharedCases.dispatch3

def vertex (i : Fin 4) : Fin 11 := ⟨i.val,by have := i.isLt; omega⟩

theorem sliceEdges (i : Fin 4) : ∀ u v : Fin 10,
    G.Adj ((vertex i).succAbove u) ((vertex i).succAbove v) ↔
      (u.val,v.val) ∈ @k7 ⟨i⟩ ∨ (v.val,u.val) ∈ @k7 ⟨i⟩ := by
  fin_cases i <;> decide +kernel

theorem sliceEvaluation (i : Fin 4) (x : Fin 10 → Bool) : graphFun G ∅ ((vertex i).insertNth false x) = true ↔
    ∃ u v : Fin 10, (u.val,v.val) ∈ @k7 ⟨i⟩ ∧ x u=true ∧ x v=true := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    have ea : a≠vertex i := by intro eq; subst a; simp at ha
    have eb : b≠vertex i := by intro eq; subst b; simp at hb
    obtain ⟨u,rfl⟩ := Fin.exists_succAbove_eq ea
    obtain ⟨v,rfl⟩ := Fin.exists_succAbove_eq eb
    rw [Fin.insertNth_apply_succAbove] at ha hb
    rcases (sliceEdges i u v).mp edge with h|h
    · exact ⟨u,v,h,ha,hb⟩
    · exact ⟨v,u,h,hb,ha⟩
  · rintro ⟨u,v,edge,hu,hv⟩
    refine ⟨(vertex i).succAbove u,(vertex i).succAbove v,(sliceEdges i u v).mpr (Or.inl edge),?_,?_⟩
    · simpa using hu
    · simpa using hv

theorem four_lower (certified : Certified) (v : Fin 11) (C : Circuit) (hv : v.val<4) (legal : IsAO2 10 C)
    (relation : ∀ x : Fin 10 → Bool, circuitFun 10 C x = graphFun G ∅ (v.insertNth false x)) : 19≤C.size := by
  let i : Fin 4 := ⟨v.val,hv⟩
  have same : vertex i = v := Fin.ext rfl
  have mono : Monotone2 C := fun g h => ⟨legal.1 g h,by have := legal.2.2 g h; omega⟩
  by_contra h
  apply @lowerFromAbelianTarskiArtSabintsev ⟨i⟩ (cellsAt i) (certified i) (dispatchAt i)
  refine ⟨C,mono,by omega,fun x => ?_⟩
  change circuitFun 10 C x=true ↔ _
  rw [relation x,← same]
  exact sliceEvaluation i x

end PriorG11.Bounds

namespace PriorG11.Proof
open SharedCases Bounds Learning Blocks

theorem certified (all : Successful) : Certified := by
  intro i b member
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem member
  have eq : (cellsAt i).getD j default = b := (List.getD_eq_getElem _ _ hj).trans he
  have checked : whole (before i+j) (@reason ⟨i⟩ b) (@active ⟨i⟩ b)=true := by
    apply List.all_eq_true.mpr
    intro s hs
    have result := all i j hj s (List.mem_range.mp hs)
    simpa only [atBlock, eq] using result
  intro v allowed
  have admissible (key : Nat) : holds v (@reason ⟨i⟩ b key) := by
    by_cases h : @active ⟨i⟩ b key=true
    · simp only [reason,if_pos h]
      obtain ⟨lit,member,agreesWith⟩ := allowed key h
      exact ⟨lit,member,agreesWith⟩
    · simpa only [reason,if_neg h] using holds_tautology v
  exact Bool.noConfusion (checked.symm.trans (whole_sound admissible))

end PriorG11.Proof

namespace PriorG11.Bounds
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def evaluation (x : Fin 11 → Bool) := edges.any (fun e => x ⟨e.1%11,Nat.mod_lt _ (by decide)⟩ && x ⟨e.2%11,Nat.mod_lt _ (by decide)⟩)
theorem graphRead (x : Fin 11 → Bool) : graphFun G ∅ x = evaluation x := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false, decide_false, Bool.false_or, decide_eq_true_eq,
    evaluation,List.any_eq_true,Bool.and_eq_true_iff]
  have inRange : ∀ e ∈ edges, e.1 < 11 ∧ e.2 < 11 := by decide
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    rcases (adjacent a b).mp h with h | h
    · exact ⟨(a.val,b.val),h,by simpa [Nat.mod_eq_of_lt a.isLt] using ha,by simpa [Nat.mod_eq_of_lt b.isLt] using hb⟩
    · exact ⟨(b.val,a.val),h,by simpa [Nat.mod_eq_of_lt b.isLt] using hb,by simpa [Nat.mod_eq_of_lt a.isLt] using ha⟩
  · rintro ⟨⟨a,b⟩,h,ha,hb⟩
    have bounds := inRange (a,b) h
    refine ⟨⟨a,bounds.1⟩,⟨b,bounds.2⟩,(adjacent _ _).mpr (Or.inl h),?_,?_⟩
    · simpa [Nat.mod_eq_of_lt bounds.1] using ha
    · simpa [Nat.mod_eq_of_lt bounds.2] using hb

def packed (x : Fin 11 → Bool) : Bool :=
  ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).any
    (fun i => x (Fin.ofNat 11 (i/11)) && x (Fin.ofNat 11 (i % 11)))

theorem graph_packed (x : Fin 11 → Bool) : graphFun G ∅ x = packed x := by
  rw [graphRead]
  rfl

theorem packed_lower (certified : Certified) (v : Fin 11) (C : Circuit) (hv : v.val < 4) (hC : IsAO2 10 C)
    (hF : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = packed (v.insertNth false x)) :
    19 ≤ C.size :=
  four_lower certified v C hv hC (fun x => (hF x).trans (graph_packed _).symm)

end PriorG11.Bounds
namespace PriorG11.Join

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def append (P T : Circuit) : Circuit := ⟨P.gates ++ T.gates, T.output⟩

theorem append_size (P T : Circuit) : (append P T).size = P.size + T.size := by
  simp [append, Circuit.size]

theorem append_eval (P T : Circuit) (x : List Bool) :
    (append P T).eval x = T.eval (P.wires x) := by
  simp [append, Circuit.eval, Circuit.wires, List.foldl_append]

theorem append_legal {n : ℕ} {P T : Circuit} (hP : IsAO2 n P)
    (hT : IsAO2 (n+P.size) T) : IsAO2 n (append P T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact hP.1 g h
    · exact hT.1 g h
  · intro j hj i hi
    change j < (P.gates ++ T.gates).length at hj
    change i ∈ ((P.gates ++ T.gates).getD j ⟨GateOp.or,[]⟩).inputs at hi
    by_cases hp : j < P.gates.length
    · rw [List.getD_append _ _ _ _ hp] at hi
      exact hP.2.1 j hp i hi
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hp)] at hi
      rw [List.length_append] at hj
      have h := hT.2.1 (j-P.gates.length) (by omega) i hi
      simp only [Circuit.size] at h
      omega
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact hP.2.2 g h
    · exact hT.2.2 g h

theorem wires_length (P : Circuit) (x : List Bool) : (P.wires x).length = x.length + P.size := by
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have go : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length+gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g t ih => intro w; simp only [List.foldl_cons, ih, step, List.length_append,
        List.length_cons, List.length_nil]; omega
  exact go P.gates x

end PriorG11.Join

namespace PriorG11.Formulas

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def op (conj : Bool) : GateOp := if conj then .and else .or

def combine (conj left right : Bool) : Bool :=
  if conj then left && right else left || right

theorem op_eval (conj a b : Bool) : (op conj).eval [a,b] = combine conj a b := by
  cases conj <;> simp [op, combine, GateOp.eval]

def root (size : ℕ) (conj : Bool) (a b : ℕ) : Circuit := ⟨[⟨op conj,[a,b]⟩],size⟩

theorem root_legal {base a b : ℕ} (conj : Bool) (ha : a < base) (hb : b < base) :
    IsAO2 base (root base conj a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain rfl : g = ⟨op conj,[a,b]⟩ := List.mem_singleton.mp hg
    cases conj <;> simp [op]
  · intro j hj i hi
    have j0 : j = 0 := by change j < 1 at hj; omega
    subst j
    change i ∈ [a,b] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · intro g hg
    obtain rfl : g = ⟨op conj,[a,b]⟩ := List.mem_singleton.mp hg
    rfl

theorem root_eval {base : ℕ} (conj : Bool) (a b : ℕ) (w : List Bool) (h : w.length = base) :
    (root base conj a b).eval w = combine conj (w.getD a false) (w.getD b false) := by
  subst base
  change (w ++ [(op conj).eval [w.getD a false,w.getD b false]]).getD w.length false = _
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  exact op_eval _ _ _

theorem wires_extend (C : Circuit) (w : List Bool) : ∃ t, C.wires w = w ++ t := by
  let step := fun (l : List Bool) (g : Gate) =>
    l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]
  have keep : ∀ (gs : List Gate) (l : List Bool), ∃ t, gs.foldl step l = l ++ t := by
    intro gs
    induction gs with
    | nil => intro l; exact ⟨[], (List.append_nil l).symm⟩
    | cons g gs ih =>
      intro l
      obtain ⟨t, ht⟩ := ih (step l g)
      let a := g.op.eval (g.inputs.map fun i => l.getD i false)
      exact ⟨[a] ++ t, ht.trans (List.append_assoc _ _ _)⟩
  exact keep _ _

theorem wires_old (C : Circuit) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (C.wires w).getD i false = w.getD i false := by
  obtain ⟨t,ht⟩ := wires_extend C w
  rw [ht, List.getD_append _ _ _ _ h]

theorem append_wires (A B : Circuit) (w : List Bool) :
    (Join.append A B).wires w = B.wires (A.wires w) := by
  simp [Join.append, Circuit.wires,List.foldl_append]

def merge (base : ℕ) (conj : Bool) (A B : Circuit) : Circuit :=
  Join.append (Join.append A B) (root (base+A.size+B.size) conj A.output B.output)

theorem merge_size (base : ℕ) (conj : Bool) (A B : Circuit) :
    (merge base conj A B).size = A.size+B.size+1 := by
  rw [merge, Join.append_size, Join.append_size]
  rfl

theorem merge_legal {base : ℕ} (conj : Bool) {A B : Circuit}
    (hA : IsAO2 base A) (hB : IsAO2 (base+A.size) B)
    (oa : A.output < base+A.size) (ob : B.output < base+A.size+B.size) :
    IsAO2 base (merge base conj A B) := by
  apply Join.append_legal (Join.append_legal hA hB)
  rw [Join.append_size, ← Nat.add_assoc]
  exact root_legal conj (by omega) ob

theorem merge_eval {base : ℕ} (conj : Bool) (A B : Circuit) (w : List Bool)
    (hw : w.length = base) (oa : A.output < base+A.size) :
    (merge base conj A B).eval w = combine conj (A.eval w) (B.eval (A.wires w)) := by
  rw [merge, Join.append_eval, append_wires, root_eval]
  · have short : A.output < (A.wires w).length := by rw [Join.wires_length,hw]; exact oa
    rw [wires_old _ _ _ short]
    rfl
  · rw [Join.wires_length, Join.wires_length,hw]

def build {n : ℕ} (base : ℕ) : DMFormula n → Circuit
  | .lit i _ => ⟨[],i.val⟩
  | .and f g => let A := build base f; merge base true A (build (base+A.size) g)
  | .or f g => let A := build base f; merge base false A (build (base+A.size) g)

theorem build_output {n : ℕ} (f : DMFormula n) (base : ℕ) (hb : n ≤ base) :
    (build base f).output < base+(build base f).size := by
  cases f with
  | lit i _ => change i.val < base + 0; have := i.isLt; omega
  | and f g => simp only [build,merge_size]; change base+_+_ < base+(_+_+1); omega
  | or f g => simp only [build,merge_size]; change base+_+_ < base+(_+_+1); omega

theorem build_size {n : ℕ} (f : DMFormula n) (base : ℕ) :
    (build base f).size+1 = f.leaves := by
  induction f generalizing base with
  | lit _ _ => rfl
  | and f g hf hg | or f g hf hg =>
    have ha := hf base
    have hb := hg (base+(build base f).size)
    simp only [build,merge_size,DMFormula.leaves]
    omega

theorem build_legal {n : ℕ} (f : DMFormula n) (base : ℕ) (hk : n ≤ base) :
    IsAO2 base (build base f) := by
  induction f generalizing base with
  | lit i b =>
    refine ⟨?_, ?_, ?_⟩
    · intro g hg; exact (List.not_mem_nil hg).elim
    · intro j hj; exact (Nat.not_lt_zero _ hj).elim
    · intro g hg; exact (List.not_mem_nil hg).elim
  | and f g hf hg | or f g hf hg =>
    have large : n ≤ base+(build base f).size := by omega
    exact merge_legal _ (hf base hk) (hg _ large) (build_output f base hk) (build_output g _ large)

def positive {n : ℕ} (x : Fin n → Bool) : DMFormula n → Bool
  | .lit i _ => x i
  | .and f g => positive x f && positive x g
  | .or f g => positive x f || positive x g

theorem positive_rec {n : ℕ} (x : Fin n → Bool) (f : DMFormula n) :
    positive x f = DMFormula.rec (fun i _ => x i)
      (fun _ _ a b => a && b) (fun _ _ a b => a || b) f := by
  induction f with
  | lit _ _ => rfl
  | and f g hf hg | or f g hf hg => simp only [positive, hf, hg]

theorem build_eval {n : ℕ} (f : DMFormula n) (base : ℕ) (x : Fin n → Bool)
    (hk : n ≤ base) (w : List Bool) (hw : w.length = base) (hx : ∀ i, w.getD i.val false = x i) :
    (build base f).eval w = positive x f := by
  induction f generalizing base w with
  | lit i _ => exact hx i
  | and f g hf hg | or f g hf hg =>
    let A := build base f
    have ha := hf base hk w hw hx
    have bigger : n ≤ base+A.size := by omega
    have new_len : (A.wires w).length = base+A.size := by rw [Join.wires_length,hw]
    have bank (i : Fin n) : (A.wires w).getD i.val false = x i :=
      (wires_old _ _ _ (by rw [hw]; exact lt_of_lt_of_le i.isLt hk)).trans (hx i)
    have hb := hg (base+A.size) bigger (A.wires w) new_len bank
    simp only [build]
    rw [merge_eval _ _ _ _ hw (build_output f base hk),ha,hb]
    rfl

theorem formula_tail_witness {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ)
    (lower : ∀ C : Circuit, IsAO2 n C → (∀ x, C.eval (List.ofFn x) = f x) → s ≤ C.size)
    (P : Circuit) (hp : IsAO2 n P) (T : DMFormula (n + P.size)) (room : P.size + T.leaves ≤ s) :
    ∃ x : Fin n → Bool,
      positive (fun i => (P.wires (List.ofFn x)).getD i.val false) T ≠ f x := by
  by_contra! h
  let A := build (n+P.size) T
  let C := Join.append P A
  have legal := Join.append_legal hp (build_legal T (n+P.size) le_rfl)
  have agrees (x : Fin n → Bool) : C.eval (List.ofFn x) = f x := by
    let z := fun i : Fin (n+P.size) => (P.wires (List.ofFn x)).getD i.val false
    have hz := build_eval T (n+P.size) z le_rfl (P.wires (List.ofFn x))
      (by rw [Join.wires_length,List.length_ofFn]) (fun _ => rfl)
    exact (Join.append_eval P A _).trans (hz.trans (h x))
  have hl := lower C legal agrees
  have hs : C.size = P.size+A.size := Join.append_size _ _
  have ht : A.size+1 = T.leaves := build_size T _
  omega

end PriorG11.Formulas

end PEqualNP.Outside.L_meta_18560

open PEqualNP.Outside.L_meta_18560.PriorG11 in
theorem PEqualNP.Outside.L_meta_18560 : ∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (10 : ℕ) x2 →       x2.size ≤ (12 : ℕ) →         ∀ (x6 : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)),           x6.leaves ≤ (7 : ℕ) →             ∃ (x8 : Fin (10 : ℕ) → Bool),               have x9 : Fin ((10 : ℕ) + x2.size) → Bool := fun (x9 : Fin ((10 : ℕ) + x2.size)) => (x2.wires (List.ofFn x8)).getD (↑x9) Bool.false;               PEqualNP.MetaComplexity.DMFormula.rec (fun (x10 : Fin ((10 : ℕ) + x2.size)) (x11 : Bool) => x9 x10) (fun (x10 x11 : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)) (x12 x13 : Bool) => x12 && x13) (fun (x10 x11 : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)) (x12 x13 : Bool) => x12 || x13) x6 ≠                 have x10 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x8;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (11 : ℕ) (x11 / (11 : ℕ))) && x10 (Fin.ofNat (11 : ℕ) (x11 % (11 : ℕ))) := by
  intro v P hv hp hb T ht
  let f := fun x : Fin 10 → Bool => Bounds.packed (v.insertNth false x)
  have lower (C) := Bounds.packed_lower (Proof.certified Proof.successful) v C hv
  obtain ⟨x, hx⟩ := Formulas.formula_tail_witness f 19 lower P hp T (by omega)
  refine ⟨x, ?_⟩
  rw [Formulas.positive_rec] at hx
  exact hx
