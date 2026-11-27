import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18015

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
abbrev EightWords (α : Type) := α × α × α × α × α × α × α × α

def memberOfEight {α : Type} (i : Nat) (row : EightWords α) : α :=
  if i < 4 then
    if i < 2 then (if i = 0 then row.1 else row.2.1)
    else (if i = 2 then row.2.2.1 else row.2.2.2.1)
  else if i < 6 then (if i = 4 then row.2.2.2.2.1 else row.2.2.2.2.2.1)
  else (if i = 6 then row.2.2.2.2.2.2.1 else row.2.2.2.2.2.2.2)

abbrev WordPage := EightWords (EightWords (EightWords Nat))

def page0 : WordPage :=
(((0x270d001a110009090000,0x4f0b00441000340d00,0x5006a0500650a005b0c,0x7a04007603007304006f,0x8906008305007e0400,0x9009a09009104008d04,0xbf0500ba0800b20f00a3,0xc90300c60400c20300),(0x300d50400d10400cd04,0xe30500de0300db0300d8,0xee0300eb0400e70400,0x200fa0700f30200f103,0x30400ff0000ff0300fc,0x10d0401090401050201,0x3011b04011705011205,0x2704012303012002011e),(0x12e00012e04012a0301,0x1013802013603013305,0x4605014103013e050139,0x103014f0601490301,0x1000000000001000000,0xc0000000000080000002,274884199168,35184380608640),(0x80000300180b200,0x210080001001a0fa0080,0x4000001608100c000,0x700b84c40a00900,0xcc3898274060048001,0x804002400001,0x10080200120000080,0x1006010009000004000),(0x420800480000200000,0xa1048024000010000001,0x828012000200000001e0,0x60090000080000718058,0x4880002000000f06081,0xcc0001000028844c20d0,0x8000165e32107004,0x4000003319503c039e),(0x2000001c8cc422024c00,0x180ec6721201260000,0x8e370098093000010,0xe4e1e084c049a0000800,0x79008280273100040001,0x89416016790002000162,0x20c00ccc00400003fd74,0x6806ae0020000000fe49),(0x37a0000400000000048,0xbd000020000000804036,0x80001000000140301b01,0x200000002009a0d80de,0x4000001c05107406f40,0xe82a83e037a000,0x9d7c7caf42101bd00002,0xaa44a2b1180deda0019b),(0x255d88982c96d000fa4e,0x32444e296d68004efd1f,0xb62817b8800020000e99,0x158bfe5200100337d499,0x4618a5000801b0cf2e4a,0x39800004000007f7290b,0xc00002000000000285e3,0x1000000040203119c)),
((0x80000006018188ce60,0x10000d0348c4673000,0xc82086433990840,0x32c7c7143419ed000020,0x403921b0cf6d4001003,0x25650e07b3c000080000,0xc70743d9f58004e791f2,0x43e2b52000800400012a),(0x15a900001080000c97f,0xad4a900080d3f4a4c3a2,0x63500049df897a7dd108,0x8001e00000403f488857,0x100000000014463155,0x800000020102418ae00,0x1b00c120c570000,0xe00849062b800004),(0xfc7c4a449315c0000200,0x402592598ae5c001ec9c,0x4a5130d8340000800000,0x449c6c1b68007b275522,0x4f43af000020015711a5,0xa1d7c204000edfc91750,0x3a2c0009d29424ae2a27,0x30840000000267309451),(0x201c16943caca4932,0x1f0095cca5eb25549a7a,0xbb271e652b12b2556403,0x3c95c95d2ae2d000,0x2ecb08b0a284000040,0x145a514200002000,0x20102e28a10000100000,0xc171450800008000000),(0x8b8a28400004000001d0,0xe5142ac0020f9e30f876,0xa1d56001003e84887d45,0x4ed0009c16fe4a56a302,0x400000272b89895f,0x217fdf1919e8c6b576,0x1000000d0d06655abb80,0xa188a469a342d8e8000),(0x85936c1a96c7490028,0x28d4b6710800400,0x40206c5b50000020000,0x28362da800001000000,0x49b16d4000030000000e,0xdab6a108020004e00907,0x5ba89c002009e5858628,0x3100001000000443326f),(0x80000800000241a8382e,0x13c0009d130dc1c1718,0x2000008a0724e0b8c40,0x13aec64784715c62000,0x80343e939ae314e001,0x108123d1d17b0e000400,0x28ecbd9d58004028,0x4020785fc50000200000),(0x683c2fe2800010000000,0x9e17f1620080002000c0,0x2bfe528004001c40a088,0x920000200000088484f,0x900001000080482607a6,0x2780027a261403d304,0x4000fe140a89e98248,0x900b8628f6c12400)),
((0x8c4a045947d60928802,0x83fb057d40010,0x10081fd8aa80000800,0x40060fec554000040000,0x1f47f62aa00002000000,0x240b1554e00100400034,0xd8f0400008000010010,0xc7820000400000000052),(0xc100002000000080410a,0xc8001001094142108563,0x8000001212242b1e0,0x400d150c0f921d92100,2822541185792,0x40208b655b00002,0xf6140e845b2ad8000100,0xb080a2d956ea000822e),(0x2918cd5a0013c0013b,0x208e66ad000020000000,0x47335680001000000040,0x99ab670008009a41a148,0x5c000040000000004a3,0xe00002000000080411ed,0x4f0002b44c0408f682,0x80015a2804147b4170),(0x40000000004a41a0ba50,0x804122d0980000,0x4804091684c000020,0xa2804148b42600010000,0x4a49a132500080013,0x4126d0d400004000000,0x93686a0000200000008,0x9b435000010000005403),(0xa1a800008000002c0214,0xd510040001001703ca51,0x2000000000252ad0,0x100000004020966897,0x8000a0340b04b344b80,0x1e1c080a59a25e100,0x861584852ed1cd08004,0x2044c09869078800200),(0x94c348c4a010006a,0x8265a9880000800000,0xa132d4c4000040000001,0x996a620031e0031d8c00,0x35314e0010008ec64202,0xd9c0000800000000094d,0xe00004000000100826da,0x40020031d8d022136d6c),(0x15973b6044349b6b679,0x800000000094eb5ed5a0,72201053388931072,0x1500613cddd4000040,0xac0449e6eea00002000,0xa0325037750000100000,0x65289bba8000d80006a5,0x948ddd52000400037310),(0x66f66ac00276f24991fc,0xde65600109f11d05132a,0xc69001007ab6848e353b,0x40000000005aa9f3,0x2000000080415afab6,0x1000000b0030ad7d5b00,0x6e5a02a56bead8000,0x3006d2bdf56c000e8)),
((0x499204962fab72000400,0x5182b37de6ac00286e0,0x9535a453250001000209,0xdade2d46900080067c84,0x75185600004002846c4a,0x8c2b0000200000000021,0x158000100000004020ba,0xe900080006a5c0685d46),(0x4151492f0a5aea30a,0x20a8a49808a57b19535,0x54524c4592be8e0ea80,0xa29264f415fc7b9d6001,0xfd3785cb0241fa800082,0x9c48498343ef5800435f,0xa444c3a471ac0021affa,0xda62d35d806c00035fce),(0x31e9aee900080002a814,0x7555d500040942948a8a,0xb080271202be024d4859,0x40601000010142a72cca,0x10080000b4a355166d58,0x4000000000433aac46,0x2000000080419d563800,0xd4b4040ceab1c0000),(0x6a02a67558e0001b0,0x36018b42ac700000800,0xb8845a35638000040000,0x922d2ab1ca4004005801,0x969d6fbd2002001420e0,0x52c6900000800600e049,0x63480000400000000043,0xa40000200000008041a9),(0x400400008008c0c0d4b1,0x8000007206a6a58d2,0x10ff3a0b8b5ac6e40,2864579031041,0x4020d9b21700002,0x40f02686cd90b8000100,0x4b66c85e30008000,0x8041b567680000400000),(0x30dab3b4000020000000,0x6d59da00001000000ec0,0xeced0002000000078069,0x768000040000000004b6,0x40000200000008041b96,0x1000075340b0dcb3b,0x8000000000a6e59da4,0x4000000100837acf3400),(0x1e8061bd679a0000,0x1041f4deb3cd000020,0xa7059e6c0100000,0x100838ad08c000080000,0x61c5684600004000000,0xe2b42300002000d91f8,0x15a11c6100000001001e,0xd2d000008000000000a7),(0x68000040000001008392,0x2000d71f0061c969,0x100000001081b0e4b4b4,0x8000000000a725a5a42,4512643440246784,0xf00200321cd6a0800004,0x4014e6b5048820004,0x7e020745ab4000010000)),
((0x243a2d5a2200200024c,0x25d16aeb400040000e57,0xe9b5ab00002000000000,0xdad580001000000f4020,0x6ac00008000007c01a74,0x60000400000000053aed,0x200000008041db6b5,0xdf005a950c0e0edb5ab0),(0x8000008a08976dad5c00,0xe9d460893bad7121007,0x25e16b9d400040,0x910040f1b68000002000,0x206078db404400400049,0x3d3c6da3630080000009,0x5e76d7348004053f96b0,0x4b6dc000020000000802),(0xb6e0031f0144951c0f0f,0x72800080a24a901597a5,0x400040382d491ccbd6db,0x200000000025ed7017,0x10015e130020f7bb3400,0xa24ab00607bdd9a0000,0x4bdeecd2018f8,0x8041f176960000400),(0x4c030f8bb4b000020000,0x97c5da580001000001,0x3e6ed2c000080000000,0xf3769638004000045a01,0xbb600000200000000021,0xb00000100000004020f9,0xc780510a9c0807cdd,0x63c028854f078be6ed8),(0x1e01442a80585f576c00,0xa215443a2fbbb60003,0x390aa45717e5db00018f,0x4bf6ed82800080,0x298041fd806600004000,0x12fec0330000200000,0x207fe019800010000000,0x3ff00cc0008000824940),(0xf806700c7c04ae74b03c,0x4a0000200000000025f,0x5000010000000402100c,0x18f80a24a9808080602,0xc7c051254d078c030128,0x20000000002603809400,0x281dc12102c04a0000,0xa8160254a0010),(0x1008413031c0000800,0xb01a209818e000040000,0x14304c0c780020000002,0x982e06f8000100000190,0x1b037c00008000000000,0x81be0000400000010084,0xdf00002000002a00620d,0x800ba0000815805306c0),(0x8000000000883e06f,0x4000000100841f037c0,0x8192ab8ae20f81be000,0x16858307c0dfa0002,0xce2e28462430000100,0x442b121a00008000,0x804215891c0000400000,0x310ac48e000020000000)),
((0x85624700001000001500,0xf123a0000800000ae059,0x94600004000006e03142,0x300002000000000221b8,0x1000000040210dc4a,0x8f80a24ab008086e2518,0xc0512559078c37128c01,41908298973383),(0x40210fc4a3000020,0xb401887e25180001000,0x401143f128c000080000,0xa62389460037c005396,0x512c4a30000200006b38,0xa6251800010000000001,0x128c0008000000c60188,0x4600004000006d018c53),(0x20000000002a2b89,0x10000000402117c4a3,0xd808f4a1e0608be25180,0x47a51019545f128c01f,742413357514756,0x40211bc8270000200,0x1c0608de413800010000,0x4c6f209c007f8023da),(0x8239904e000040000000,0x1cc8270027e0027db400,0xe41380200000001a4063,0x9c0000800000d403a8e,0xe00004000000000547f2,0x20000000804243904,0x7f0053e5ac06121c8270,0x8045ead806190e413803),(0x22f56d048c8b209c01bf,0x2647904e00dfc0,0x402124c82700002000,0xe0189264138000100000,0xcc93209c0000800000c,0x24b904f18020000a06f0,0x5c83700010001783800a,0x41b80001000001b80112),(0xdc00008000000000892e,0x4000000100849720,0x2000000f00624b906e,0x13cbfc7d50525c83700,0x1fffe6eb8493e41bc608,0x5caf3ed408000,0x80425d9f6a0000400,0x740312ecfb5000020000),(0xa9767da80001000000,0x84c33ed4000080000000,0x619f6a00004000000100,0xcfb50000200000108062,0xdac608010affc88ff530,0x20800043ffe7092c9967,0x40000000005cdb560,0x20000000804273abbc0),(0x8003139d5de000,0xa9ceaef00001,0x10084ef5778000080,0xbb832277abbc00004000,0x3353bd5dea000202b96,0x4a9eeb6fd0001015cb5e,0x4ff5fee800080ae5af22,0x3b1e75000404fb97a215)),
((0xbf0000020000000002a8,0x8000010000000402143d,0x4f80165a50060a1edf,0xa00040001150f6fc0,0x200028010050040008,0x140008000a200014010,0x4000500200a00800100,0x8001000040008000200),(0x2000414010010000,0x20002804000004020,0x40008000200800001,0x800050020000080010,0x800180014020028020,0x28020004000100200a,0x10002000500010000402,0xa004000800140100280),(0x1002801000200050400,0x1900400a00400080014,0x2fffe000a40000,0x32080000009000000048,0xa00401000014000800,0x40800280100100000880,0x50010320040004006,0x80014010028010002),(0xa002014008001000c8,0x40000281000500200200,0x20004000a2000140080,0xf00054000000c8020050,0x80200281440000001fff,0xa0800140080010002,0x800004400050020080,0x200020032040014008),(0x2014008001000c900019,0x4000800140004000a00,0x4000a2000000080400a0,0x10000000402005002000,0x21000280100020005,0xa050001000c82000,0x400800002004028011,0x4000a10000000801000),(0x8001000280200500200,0x50020004000a0080140,0x20001400804000028020,0x4800050020100000a,0x40c8010002001904000,0x802000028002000640,0x50020004000a100014,0x10001140080100002802),(0xa004000800140004000,0x200001010000008008,0x80080a00400080014,0x10050020004000a04000,0x1008000008100000280,0x80000400400002000428,0x40020280100020005000,0x500010a0040400001),(0x800014004028010002,0x8010002000500010a004,0x400a0040200001400402,0x14020028010010000500,0x81000a004008000,0x4040050020020000a010,0x10010000080106400,0x800004000800140020)),
((0x200040001000200008,0x80000080200000400080,0x4004000020004000100,0xe1401001000008008000,0x20023200019002001,0x50020004380a00020005,0x4014008002000280080,0x4040050020008000a0),(74308294424395776,0x52000002303ffc701408,0x118080028010002000,0x40005000100028001,0xa0040010001400802801,0x400008c1000000080800,0x4602000a004000800140,0x50020004000a3fff00),(0x1004014028002000c810,0x4010000024000140,0x800001004000008020,0x1900403200500000064,0x40000640100c80140000,0x320010015e0001320040,0x3200400807064000400,0x40040000100200000810),(0x14028002000c80008006,0x8500a0004c8010040,0x500020000800100004,0x1000040008000200fe0,0x2000400010200000280,0x20000800100004200028,0x80080000200080005000,0xe00201c0080010003),(0x100038008070020004,0x20004000e00201c008,0x201c0080010003800807,0x40008001c0004000e00,0x38010002000700100e0,0x80010003800800002004,0x1c0040000100201c00,0x80000088000e0040008),(0x400800002004000010,0x4000100200000801000,0x8010000040080000200,0x2004000010020000,0x200000800100064008,0xc80080000200400001,0x4000108000a0080020,0x800100004008000020),(0x8050020004000a020000,0x10020000500010002800,0x4008000020400280,0x402805000200190010,0xc0080008003800800002,0x8001c0004000e00021,0x10080000280400e0040,0x1050040200000a000414),(0xa0100000100200002800,0x28040050040008000,0x2000002010014010002,0xe00800000804000004,0x40320040008006400040,0x20004003203ff007d00,0x200192000050c8020000,0x80201900240002805000)))

def page1 : WordPage :=
(((0x32008014028001000c,0x1ff803e8020190020004,0x86401000001000200190,0x14028001000c900002,0x14000800640100c80140,0x3c010020000780400a0,0x84000f0040080001e100,0x1e10003c0100200007),(0x20000784000f0040080,0x436e1536aa004000c050,0x10a8a84142b3806d41ad,0x8a8a8a85155728a954aa,0xaa5554955452d52a8a8a,0x610e1c3049214941612a,0x554d52abc183b9839b98,0x6402a01200300140015),(0xf8ffbdff6bfb3fd4fe78,0x7d53ea7f35fcd7e67f29,0x5e84f406e83eb5f59fac,0xb747f9bfb9fb4ffa7fd1,0x3fe5ff257913c81e3af1,0x6ef87bc17e0af02f47bd,0xa9dd4aea0f4c7bbbdbab,0xe88741b9e3a5abed5a6b),(0x6d33659fcd747fa33d18,0x4e586a674b3919c6cdf6,0x7b90d518fccfd679bdcc,0xc5dd8e55722bf18e8c72,0x4531a9f95faaef53797b,0x3d3fca7d53c29b95dca6,0x6a6b50b910fa9de4ea27,0x5d0fd18643f19ff50e68),(0x5e64f323980d0c683b3f,0x1795fca7e507281930c0,0x25647b21f900f45f92fc,0xff77f6c1df727693e8af,0xfc37d1ba0d80bc036016,0x7a03401fa27c12f8b7c4,0xff2078032018c0f20f80,0xc3963e36efdf4ef8ff9f),(0x3958aa5429a0a4350c71,0xe3e3ff8f801f8f8f3f84,0xc7f1fe007c7ff8ffc780,0xf1018f8ff8e038f1f003,0x80006000c78f00318f,0x7ef7f7afe87f14001100,0xbbedfbd7dd7f3af987e1,0x6afb579af487a3fceda5),(0x4ef257907c81e3bd4d69,0x966fb3419f2cf943c9fe,0xdabf0cf843c15e00effe,0xf55baabd54ea0f727b81,0x3d00e7ff3af72b955c8a,0xa6553a2dd15e8a744fa0,0x273d3e6b7357981cbfdc,0x2726b92bc70e35e54f2),(0x7a9bd3de2ef13521c14e,0xdcaee53727e4fbe7ef57,0x3515a89d6d6b67689b35,0xad2cf92b495a9ad4cea6,0x1b98d995cca67d6d13a5,0x55caa654f2a194ffc374,0x4171e3f85fa2ef1770b9,0x8b5c8ae45321f90ec836)),
((0x606701fd01c2ce35319f,0x37cff207403981800c0d,0x872ff8ff63fa7fdf6afb,0x1f7be7df2efe79798bb,0xb8d53aa95540f9b6ddad,0x214d64718f7af9d7dacf,0x18307061b3491f6e557,0xff70f00383ee1fef0ec),(0xf060060ec3e86007b87b,0x100383fbc3ee18014361,0xc000002e08001bc3bc3a,0xf800304000001000000e,0x7affe7bf3cf9dfc7ff3b,0x3d40eaffb77db9edbf6d,0x71fb8f5c61e70737b98,0x3b99bccd660b4fda01e0),(0x61d4fee79722bd1667b3,0x4f7262970cb8e9c14dca,0x7cdbe69f07002900c9f2,0x61e0c0342eaafda46fa1,0x6d83a0d07d436ec3ef6b,0x2aaaaa94a4a4808103d0,0xaf7faf148802000aa955,0xa7290620830027f4d17b),(0x88394831056942d28398,0xe62910562d285a507314,0xe01f807f4b2b62d2b4a0,0x1fc03001e01fc03f800,0x387dab67001b1618694e,0xe7314aaaa68a82bea71,0xa1b7f7fafe3e576fdb72,0x13fc8d0338ec52769d26),(0x5badff7e58d62d8142d0,0x45a94e3bfcdde777d5ef,0x2f83d69b1f87d1ec7317,0x3b86d9b3e5993e4d35be,0xf331585594e35f61d36e,0x53bced3ace336cd935cc,0xd42d0940d013fcf93dcf,0x147d1d465174551343d0),(0x10662208d2b4a52748d2,0xfffefffffdfff7ee1689,3967,0xfffffe00000000000000,0xff3fd7fabf07ea00007f,0xfe69dcfb67cbf85f07ea,0xbdd57aa753e9fd1ba2f5,0xc9b92f3febfa7eafcbf6),(0xe1fc16e6bcd398f30e4f,0x3f06e07c039ff5fabf37,0xa0d71b7ebfd5f83efdb8,0x80da1740e80d35aeafce,0x59ef4d6bad359eafd4ba,0xeb4d5fabb536a4d41a40,0xfd5fa9439f73e67aff5a,0xbf54197aefd615eabcd6),(0x9bebd579af15aab2d60a,0x6bc565ac157c17eefd5f,0x5c157d75febd579af55e,0xaa8750e61c42a83feae9,0x8750e6154290d40abf56,0xc297736a6ccd89ab3526,0x9692aff5fcbf57a2ef5d,0x7aaef0cbf9772ea5b4b5)),
((0x190bc9692b22ff5fcbe1,0x83686a8d0561a42f84dd,0xc1a82d0560a406e8dc9b,0x6e4da9b43666acd0020f,0xdc9b436617cef9bf374,0xdadb0fe1f83c0740e619,0xda0fe1f83a073037f6e0,0xaac6582b1570fe1e98d2),(0x815797f2502df5b6b596,0x47c8ed1d23946a8de6e4,0x485d01217fafa5f3bdff,0x3097d2e6f7ddf021b43,0x128440e82f4a82106811,0x787c37a1bb6416454,0xe10000ff17ffc3ffc380,0x2fff87800062fff0ffe1),(0xf8000078dfc3c000387e,0xf17ff0f800007f8bffe1,0x800061f8bfe00001c5f,0xcbde3f4000022cbf,0x17bc6630d593e1000300,0x8a1c300941e8014003af,0x6a86a0a7e9f262972588,0x9ca321c82b0ac0a8a9ea),(0x80541483406801fe4c72,0x6a02800c0250921e8781,0x8a6097a5a9623a8e2268,0x8a9ea6a98a1a82a027a9,0x9c2301ac6b0ac0aeab8a,0x1cc3304a728c8718c490,0x68541483206013fe4c93,0xe0b2250921e8781d05e1),(0x21a81a02801fc7e8ba2,0x7a9aa1a7a98a5e96a429,0x4a721c431040700ac0a,0xbf9dc8f3f9bc2131cc33,4194303,0x1fffffffffffd00000,0xffe80000000000000000,0x1fc47ed4000a3fffffff),(0xf45fe17f80fdd5fc97f2,0xe7439c8e6f3be707ae9,0x67915e3b78e9e307899e,0x74c3dfbf7ebdf0f7abde,0x3c7f897539d4974f9d39,0x85ccaf43bd09f423d00f,0x1bce6e87c0df00fbfaef,0xa8aea17a76e9c7a706a0),(0x30648398ee60f97ee5c3,0x1ded58445fd994965159,0x63c3cf1e4c77f6df9b7e,0x663d21cfd767ad9c5e70,0x11f3f00f9f3d208e7997,0xc039900f1e007c2018f0,0xefe2ff00001000000618,0x6efb7f8ffc2fdeff9ffc),(0xdafa37d17e81f3ff2de9,0xf66d33419e8d6a6b4b57,0xe8ef405562831a99c0cd,0x793fc95e41f207a43d1f,0x7d16e6b655b22de5bf28,0xade57c21e0af00f7ffbd,0xabc95dcae55722b8d5be,0xaa64531a9414ee074579)),
((0xfa74139e9f4539a9b94c,0xea0f503a77d13ca9e44e,0x7a03d00e7ff3ef9f5d55,0xaf08f457a29d13e83741,0x579a9cc6e6072ff977cb,0x95e407943c21910be873,0x43f19f80fbe7d53f935c,0xbc5ddb7a3af9d40ef27e),(0x6e17709b7bdeaef537a7,0x3e4af056a2b49568adca,0xd6a67531a90d456826d1,0xdb46d2d6967495a40d4,0xe2ee16d0b9f5fa3741b7,0x2a9953ccaff17f0bf45d,0xc8ae45321f906c78e557,0xfd03e41f00f707a03cc1),(0xee07403981c80c6a633,0xfec7f53ffe07d03c81e0,0xd9be7e06b033813c07f2,0xdf3e79cfce5e5f6efb57,0xf3be7df2ef8f753bbb87,0x6ddb46d689b42d3ebef7,0x554eaa067d71eb8b5f9b,0x8f2c71e37b1a8553eb1e),(0x59cece565067e63e31e7,0xb5fdb3e59eecf1677b3b,0xe82d08410f8afbd7dabb,0xaaa2668b1e46494a458,0xe0f307c1e3ce383c2d73,0x23ff079f83f89ff1f3c7,0x183e01e0f80e0fc73c7f,0x8cfc7c1c101f89e3c1f0),(0x300083f13c783c0707f,0x3fc020000fc646001c1c,0xdb5652f5555295d4aa78,0x341580d02c0695f170de,0x50ab45b6d16b60b682a0,0x80a0340681b40506b42b,0x97491f00ac0701f00000,0xbafb2fbfbbafc2fb7bb4),(0x7f6c75c70c66c51afab3,0x762f6675eb5e766f6bb6,0xa71271af1426425a752,0x3be39be6b6eb66cbfa27,0x67b273e72662e77a73bf,0x3b7ab79b75b74aa63266,0x340334e61a61661e6266,0x57658affaefaeaae525d),(0x2bd22bf2be2b42a52a0e,0x3d1a7ea79a60352e92ad,0xd8793a6860cb9f754a24,0x27b2d1476020c4286954,0x55740d0f8090f0086c11,0x9f1f0f8f8f800000431b,0x5d5d4dcdcdbe3e2eaeae,0xa955510b8bfc7c6cecdd),(0x2c006000aa5a2955554a,0x8bfdffee5fc6fdd7e73f,0xd0fe77f2e7cfbe5df2af,0xf2178ebc71e36f177857,0xfc07df9efbf7a7ba5e46,0x5e79f3aba55db6ec9f81,0x3969cb2e55f417a03cf,0x85e3af1cf8d7c5ee6273)),
((0xdef6ebb66de06eeb76bc,0xa62d5b6ceb64fb85dc0e,0xe78b479a38d16688f4fb,0x38e9c6de353289935cfc,0x7628b137905c7fe3d71e,0x377f1bf4df931698b0c5,0xb4dd6af8d7bcbd65ea2f,0xc6d621b36d996cc3771b),(0x9e8d3ae9bb4d8aa35472,0xa769391a02cfd67db3d5,0x80f19e6cb4f9ecb43d10,0xc7ce01f3e3e418fcfe3,0xe0073e380f8fe6019e32,0x694200c0031f00398018,0xc9fb3ce6640b798e2d0,0xf8de1fc376ede7616a65),(0xc8e0fe9f83ee6f4dc0c2,0xca744b395b1ce36c2e65,0x19631c5d8b71161de3b3,0x63dc798ef1c637c6d8cf,0xbc9591f23645c8590720,0x1fffeffffdc084432664,0xfffff000000000000000,0xb005f62fc4007f080003),(0xadcd6eabb37a6f2ce99c,0x2ce44da9762ebdab9cef,0x3ae73ce17ccf95d339b7,0xfd0760ead5ae95d26a43,0xb7d2fa2858eb1111b826,0xe7fcdf97f0fdcfb7f5fe,0xfedfd7fa7f0fdffb3f5f,0x2003ffffeff9feffd7f9),(0xdffffdffffa190211000,7,0x2000a0006fffffe0000,0x3ef9f78faa7d43e00068,0x1f2af947c7be14fc87e3,0xebb55da6ed17597d4bea,0x90dc66caf97fcbbe5bf1,0xaf7573a8dd0a6e93741b),(0x83ecdd66db2f5966ca8e,0x5e32e7f8bbc5be23f0a7,0xc0fc0fe07a28e17b4bd0,0x4d3f80f81f03c0f80f03,0x4a52555254a8aa2a2ab,0x515aaacaa998cfcd0011,0x400b682da85a05a05a8,0xf2f4e7cb8f0ffd828406),(0x1fa00fe45c98f161c1b,0x70a10101003c381003f4,0xe1ffe7bf5c7e8c162848,0x9cf87ffdefd79edd7a71,0xbf66bd5875faf3e3b75e,0xf06fddaf569cd97261c1,0x7c0249bdead3a3365c98,0x7fdffbe0000000007ff),(0x2a2ffdffbe00000000,0x768360f03dffa0cbc01c,0x6000ff9673b0cc9683ff,0x940db80eb03689793248,0xc07f80ff02493338b24c,0x27279fe7f80ff01fe03f,0x49330112493264c993,0xc6efb9e7bdc06ffbfe7e)),
((0x71de001dc7001d073f,0xa7697fff1bafe9f5f840,0xeff1fbfefc207bdedf41,0x1209fef69dcf93c27877,0x3befb0003e90009beef1,0xe34da96f169e1e026200,0x169e016a5bc5a787800f,0xbfe82d4b0078780b4f),(0x686421000338001f3f80,0x86530ffdb864330eddb9,0x8e1c3c70f0f1f3c8731c,0x2e0c1012322c6e0c0c30,0x349140f38d30b8df75bd,0x7fe1e18e18431aa51,0xe83d90e81b1f05d0f81f,0xcdff9f6bbbe73fdf7bbf),(0xce71adef5ccf71edff60,0x4aa54552a8a9554ddf58,0xf003e01d1bf975f1f015,0x1f746dd7c3777e3eba7d,0xc75f1f5d3ef805d3ef80,0xa8029558e99d5d7c00df,0x782500812b6db402ad6d,0x6716499249781e0925e0),(0x1621628b174091094926,0x7b00a2f86520cb9ca10b,0x311de291eef0c40fbbcd,0x73d823148ee7dcd73180,0x1b6eef24749b629282,0x3e98080000136732200,0x800f3c0079e003cf0f3c,0xf3c0079e003cf001e7),(0x54a952a54a8a539e1e78,0x71bcf3feef062080452a,0x4200003d001b800bfd6,0x1e00ec06103001740b8,0x3f83041020410007d03e,0x7d7febbf5cfad7c6fe3,0x3df9dfce3e6ff33f97fb,0x3cf8fbc75ea2fd13e87f),(0xd47ea0f503a71cfce7a7,0xdd0ee07743d1befef693,0xc341a81d2fe96f549ba3,0x1a00ffc00ffff003fff6,0x343434340003801e0000,0x2554aaaaa49937434374,0xf5209412023044028000,0x1fa3d27a3f45e87c9f84),(0x9b8f718e53f7beefdcfb,0x4d759eb1d5fb4f28e4fc,0xe09c29b4f696d9d31a5f,0xcb2794b34624c4788b10,0x3b43ee75cdbd167aced9,0x536a4d68a4f49a91d1ea,0x6644e993d2764e48fa9d,0x446884f08e0cc1882f02),(0x9271ce35ca44e8951262,0x63cc758e304786f51c9b,0xaa254429d688d0db3b26,0x790ea245a6bfd7f2dc51,0xc498837e9f93422744c8,0x1fa3f27a0d31a3344684,0x8fbdf77ee7d8f9ff3be7,0x44063abf5e2f45e4b4fe)),
((0xe8f716d4da7b4b720230,0xb8a653ca598fd17a1f27,0x7dceb9b7a794727e4dc7,0x7fab1a5f545debb9762e,0xc4588709e0fa9d536a4d,0xd676ce59499332272623,0x6691c4e8951262445fb3,0xe23c37d34a293d26a3b4),(0xb44686d7a4ec9c93cf25,0x45febf973c2683105e13,0x7e9f929b9271ae8d712d,0xae8fc9e764cc798eb1c6,0x90721e2f45e4ac28d510,0x4460d02204111a134e89,0xcd1304af2748b1e46995,0x70f03f0f81fc00fefa38),(0x6078781f8703c303f0e0,0xe1b078703e181f0f81f8,0x7c3818583fc2c1fc183,0x781c3e07a303f87c0e1e,0x18e0763c0e1c0f0fc0f8,0xf7f6800c00e058e031f0,0xd5778f97eabedfed001f,0x6fdde9b7bfa7e4fabe57),(0x36335b376abd35b6f5e,0xebc703014020012ad000,0x2828280401c07c7dbfdb,0x666512828282a8282828,0x81a03203000033326666,0x3fb5e67cc78af13e700d,0x3fc7b8ef1ffbdf57ea7d,0xa3b4f755e9fd3bb0f20e),(0x305e1adb3b2b64ed0d1f,0xad94b2762b24e5ac3386,0xcfb8d716e25d9b3165ac,0xa3b4568a513a2141a8ad,0xb25249c85a89502afd1e,0x6665cca9833027fcf09a,0x3fc5f83d03e074098353,0x3fa794e25c239a88b102),(0xa6bcc758ab14626c55e0,0x2686565af558aa115fab,0xfc0ec99836a97d0f21d4,0xb0fdffabf53e9fd0f8d,0xa751ea1d3faa95429c5c,0x1c0360680c80c002057a,0xf15e3365ecad93b07700,0x192f25649cbfe6bccf98),(0x12f85dfe3dc778a70fe3,0xa054fd1da56e85c7b8d7,0xe18c1782b04e06a8b512,0x3b17306604dfc3786b0c,0xb312e22c408ff17eca59,0x205fd3dfa3d4768d51b8,0xa0d40f81d07daac94927,0x4b85708e6965aca5bf07),(0x1d62ac5189b10632929c,0x52272ce31c13f67c0ef3,0xa8550a21528c511402bf,0x68cc9983006fccfa1e43,0x7e1a85511634090123e6,0x1fbe8e8358c12c8a0238,0x86078781c3c0f87c0f80,0x1d07c3f60e1c0ff0f81f)),
((0xe083041e1a0d083e1a0e,0x47c0f0f81f0fe07c3a0f,0x14781f470387f81e181f,0x8683d8fc08781c3e0438,0xc6b5c403d3000fa00f81,0x13f2f211fe1c18e8b7c6,0x1ffb08f817f6f614,0xb85a2c10f86c01ffb000),(0x90c7a3b1c8bc4a22f278,0xfff8000f788fe731,0x6c001b0006c001b005,0xf91f00102a0b6c001b0,0x4d8173e1d92e99b1f15d,0x8ef1cff6deefe935d055,0xcce14bd7d6adf989e75a,0x2529494a529294a55052),(0x25d3363e2ba1f23e0025,0xddfd26ba0aa9b02e7c3b,0xd5bf313ceb51de39fedb,0x525294aa0a599c297afa,0xa8f98f8004a4a529294a,0xf7dfd741f0ae9cd87c2b,0x7acb7b319e7ad43ba397,0x802955a944b5708a54cf),(0x9d2ebe000f9f2ebe000f,0x9f3a2e8b801f2cbc3e0d,0xce401fcb9fcdbe098d8f,0x5f2e800f9f1dc00faabe,0xcd8faf7eee8e7e001fef,0x8faf5d1f3eee8e7e001f,0xc00dad7eecaebe002b4d,0xab4d9d0a6cae8e7c3e1d),(0x8b801b0fbcec8c7c1dcb,0x1f2c8c6ebc3e0dbceaae,0x2aacbc0bab4d9b0fbadd,0x5d2aacba3c09be1ffadd,0x9b2f59fc09be1fcd9b2f,0x2abeec99ce7c09a95fcd,0xbeec8e7c099dcb9fef5d,0xce7c099dcb9fed5b2f6a),(0xcc4e499dcb9fed5b2f7e,0xe5bddc01fed6f7ceabe,0x9deb5fed6f7ceabecc7a,0x2b6d4fbafcfecc4e5bc9,0x6e8e5bc01f0a4c499dc0,0x6c99dbddeb6d7aef7ecc,0xec8c6e99e94fbadd3cca,0x99dbe9403ad9e95dfafc),(0xe9402b4fbadd1f0a4c6e,0x9b3adf19fe297acc59db,0xbadd2a8a59fe294b9fcd,0x9d2abeec99fc3e294b8d,0x1fdb2cbc295ddfdd2c8d,0x1fdb3ccbad6f7cfece7c,0xe499dc01fef6abecc7a,0xeb5ffacc5bc9ad6f7cfa),(0xfafcce5be95dfcca7ed9,0x2e99fe1dc00d8fbcdf1b,0x1b1d2c8c7c0dad5d3cdf,0xca49be0faaba19fc0b80,0xce5fef5fef5fd9fe1ffa,0xca5deb6d7cfefedfef7e,0xfced7cca4c5bddeb6d7c,0x481619e97ad9dbfacc5b)))

def page2 : WordPage :=
(((0x600b114525241c740cd1,0x12823241a7c4e89b7334,0xc375650c216fabc5269c,0x2264801300200000005d,0x200804040004a4cc295,0x6d6acda966949243254a,0xdb5aa8c99965b2ad751a,0xd6d35b6b516b5aad4d4a),(0x5ad6adb5aadab5a56d6a,0x898ad92daaab36a1a5ad,0xd5d364ed526255ab6b58,0xd695a2909554a25a484a,0x5599d4c429586a324c54,0x20400128014524d6532,0x54c2a500849440000810,0x4004800880212410269),(0xc81802a04c0800f0140,0x2704808c1101f03a068,0x5001ffc1682c0540a414,0x2804c0800f01c0240300,0x880f01d0340640c0150,0x41602a05009c12824046,0x1fffff561005c0b,0x801001ffffff40000000),(0x102003c0600b01401802,0x4007c0f01a0320580a81,0xa81482804c094120230,0x80a81001e02c05005ff6,0x202303e0780d81a03205,0xfffd5840150290500941,0xfffe80000000000003ff,0xd8281208038180a04007),(0xb5da2cf66b2d92c762b0,0xe0602810060200803fec,0x4aa451a8942a0a048200,0x7b7d9ea62ad52a853a99,0x1586fe9f3f97c7e1eff7,0xcb5daad368b3596c963b,0xe1eff77b7d9ebf57a7d0,0x146a250a817e9f3f97c7),(0x416aa54aa14ea652a9,562948545439474,0x1ffdff80000000fffffd,0xa3e003ffdfff0000000,0x35a8c9405d6c3c7f8a16,0xe675bb93478138904008,0x6e3ff55feff5080c320e,0x3d9ac067a9554592c978),(0x46b759a89bcf67f148cb,0x1080743817f97e3eff9d,0xf60a2bd1e0f66e98c241,0x6337eeef437fb2dfec2d,0x51a2820510ab4208e18c,0x90704043d8d8d80d0c5c,0x64be7ff77b7d5e0065a2,0xb69e6d38ac339c65e2d1),(0xa8b21508865007030371,0x98f7f3e9e8f07b3c22b1,0xff3f8fbfd3e7f4b1da70,0x9b7b1d7eb767bdd2f8fd,0x5dac966bc6eb71a4dd26,0xb6dfeda4b2493506814c,0x2993cb65721bedaed367,0x40dc09e0d2beae9bd657)),
((0xf5819f42ae0540c40604,0x5f62f57071d0b8827a9a,0x955555555292cf474aaa,0x1442200688884501252a,0x3aa2232211ab440d08f1,0x59d4f8fcd58d06845688,0x9ce49e618b6048201f43,0x2f3ebe79cfd7080007),(0x96d425449bad6b99d600,0x44aaaaa4500011555524,0xb1f54458f4f4768ea475,0xaffc0bf75400001bdeda,0x44fd4adb5540556aaa52,0x9aa900d5dab688e8353a,0x54ac486df72f2f2010c4,0x6453f6ec9c36c022aaa5),(0xd3c632f2bf3da45a1a85,0x73de5510c49363367418,0xe001f00c13f9f4014055,0x99bba7c9b5d7c3e5d1f3,0x436551736f817d9f8bad,0xa5294a528a9937493557,0xcfc3e1f000045294a314,0x10bc21f425d1f3e1f7c6),(0x1421f6ce142519f3e1f6,0xefc00425180421f0f9f6,0x10fd1d1e12e8b805d51a,0x1800bc22e8bcdfc519f6,0xc5d005d00708be17c005,0x7402f9d6cdd5d5d1f2ef,0x56592aa2c9228409000d,0x59214a89a50b66b52a2a),(0x10050aa958842152490c,0x3c008f1e3c5a3c0000f6,0xb40796e9ad7800cb5aad,0x1e005a78e93c96433c25,0xad3c00cb1e00cb3c8f,0x433ccb1e8f008fe9ad3c,0x3c1e1e8f00e95ae95ae9,0x5ae9cb8f5a1ead00cb),(0x96b4ad785a3c96cbe978,0x43070025b443e9b4b478,0x5aad3c001e43008fb400,0x78963c8f1ee9cb8f5a3c,0x80881b4396e9073c5aad,0x56b5edda8cb9184a0419,0x928554d9579d2a8d0052,0x575a33a324d7512eaf6a),(0xe28292aaac10195a8317,0x30c3ef2bb78b51785acf,0x100800555514da83eda1,0x6737a79f978ff7b02018,0x7e36aea6f6b72f1f1707,0x4d1585d5cdb62e260e06,0xb52d251d150d7d655d55,0x46c4c34aca49c948c84),(0x5b3393f3b42c241c140c,0x9282fae2b32b23130373,0x918981d1a2120a024a22,0x1f401fe9523b2d9231a1,0x3f7c01b007d007401f40,0x7600fb006803fb007f00,0x1ec049215697e803d00,0x1efb71d803df6e203df6)),
((0xdb8eccf8807bedc76670,0xae80f7db8eccf8ae80f7,0x3e2bb62980f7db8eccf8,0x71d99f15db14fdf6e3b3,0x2bb629f1d99f15db14fb,0xc576c53cf8aed8a7b33e,0xd3e7f2b8de9d8a776c53,0xf80be02f0170160280b1),(0x7f807fc0005fc05fc05,0x40300e01e01f00fc03f8,0xdf48ac5a0514083c618c,0x7829e29701702e1f81c7,0xee95dd2bb82945407285,0x57732ee65d8993993a72,0x2f2e94e1e0b9cbdcbdf9,0x372eea5c5472e6e508a7),(0x435c4cbb132e16e29cbb,0x9c21441148f05ec43d88,0x39a211ca1ab286a28422,0xbb1165d34ce6bb473eea,0xa358959e2311761f7166,0x1f7c33177becab35a1b0,0x18680edb49264a408247,0xb54f4d11a3f4de308a52),(0x6a34839f3759bc68d885,0x22a48905148228806989,0x5953b1b2d2c98b8a28a4,0x9b4dd3534db359adb453,0xdaaced9a96ae9a9a9b56,0xb1dcda6e9b2b36d5b355,0x3b9b66d9babb56cb65d3,0xa3469716aeead2d2ecdb),(0x51a054922d8a68d14d4,0x84214805094508860114,0x42a994b85d49c6511080,0x732ee65d94ce4ca790a5,0x85d2970de25ec4ac4622,0xb372eee689ca547212a3,0xcf8997626422dc65e3a7,0x414c1a989e086f621bd9),(0xe7d17c545850a399ab08,0x6bc6a0cd780b8c239a94,0xb32aaab13a46231e37e1,0x902310791a10f633dfc6,0xae4a9a688b1f46e98250,0x8215012880bfce8354c6,0xa6ca96951969518b2a04,0xed5d4a5969a9d4d1a54d),(0x369ba6aac6e66ad972b2,0x946d96ac54d668ed3b4d,0xe2d36363b95cdd369aae,0x8428622ca18690923a30,0xaa6121800800900a2028,0xc0229555554aaaaaaaaa,0x374fa7c02e86df374fa7,0x1646cfa7e5fe166e86df),(0x50002dad80006b6a25fe,0x4f805d0dbe6e9f4f805a,0x4f804bfc2cdd0dbe6e9f,0xd6d44bfc2cdd0dee9f,0xe9f4f805b360005b5b00,0xd0dbe6e9f4f805d0dbe6,0x6d44bfc2cdd0dcbfc2cd,0xe8c005b00005b5b0000d)),
((0xd8511e01a3001b088df2,0xfcac21ca6e87c4230930,0x73e91e8d9f4462307dcf,0x6c272f3ee17cb4fc8d61,0x446c207d804c3f2d3e00,0x801611bb30909eee7d00,0x53f001bbcfe00e17bab0,0x220c51618bbab97fbb9f),(0xb1ccb4ac6951a4ca8668,0x98000000000000f0b8d4,0x27980330005b001501a2,0x26f300f3000cb002a02,0x1e026f3041c704d801a4,0x49802af3072c908c303,0xbd0612022b30a4ab0c9d,0xff9061a022390b8330f),(0xf3102d062201df10c003,0xc60a10bd0656015ea0c3,0xb0ca241159068a01a2a0,0xa228cc7712cb076e015d,0xd190d03d1427082c01,0x3800d190d070143c0832,0x83a011208d0a3145108,0x79083c01db08d1171461),(0x155d089b016228d36314,0x58165408fa01e2a8d629,0xeece186109cc026ab0da,0x4101041a4b0a9e0266b0,0x26394f7e25c8101602af,0x19e995c5e2bfa14df02,0x901de995e922c4e14f4,0x151e011a1961552ca215),(0x121533011199620d2ce8,0x2df915b0015e2962492d,0x8c2eb4162d015e296415,0x67712f9b16aa015e2965,0x996870303b170e015a21,0x8d216894306517590111,0x19a2968a2309217bd00,0x9e0115a169ec3178183a),(0x1b0601e2396a3031e018,0xd01c66011121700a357c,0x35d31c68008509703a35,0x4a35db1c6a0089097040,0x7aa238431d720226b170,0xa17aa4384f1dca004511,0x44897ae038b11f2a0111,0x15db17ae038b31f8200),(0xf20155217c483a7f2192,0x22fa0156917ca73ae122,0xb230200c9117d423aff,0x3bf5235c01e2a97d543b,0x543c8523a40119a18294,0x85613ed3263e015db183,0x19856f3ef6278b008d19,0xd1a1858d3f2627eb00d1),(0x1ea3985ba3f6c286b00,0x1b011929950344902b27,0x2d9300d199959345882d,0xad2dbb00448995c345ab,0x46252f7b015a2195c345,0xb3463d30cb00891996a9,0x96c2465131fb00cd1196,0xc196c346553293004489)),
((0x8d21cfd250d53c5b026e,0x26ec1cfe25102413f00,0xeb008d2200c05b924b07,0x5501022a3a00ce5bbf4f,0x429c9c01193214fe6279,0x579491800135121447a9,0xb9e84622805902c81d53,0xe743037e0bb7601121c3),(0x36eadae3772d6c3ce7a4,0x8f31ce60996afe2aa5b7,0xc0b00067524a0006b8cc,0x281ba0570b49b10031f6,0x23aab9cdd136bbf97d81,0x59392d81d414ca7b1b3d,0x2b16180586354c96989e,0x49ac11d7249318de7c09),(0x96a9c834e973a2225b46,0xd0cb4bc649ae70d474d8,0xb2b6b815d9325a425153,0x2ca000021388b78dc358,0xdf371000024247000068,0x29afc001258cfa4009e9,0x6dd46db0015a80cb8002,0x954d442a0d76194ab01c),(0x2804a6de18d53909c65,0x8e46861c1c0c9a606e95,0x191054506dc75e7e08a1,0xe04f0830004935155976,0x758625a0000824b30d28,0x5e6b5099e6c000426abd,0x4862c9c708c4b4000004,0x40d1488e1a58539a289),(0x9d0b501b08be4e62e0f5,0xc75e7e056188c4194224,0x2d930d39a3d045b49351,0x15820c41571c6218289,0x4d26a10815225955d80,0x10b28c78e34f65f4116e,0x9757c1c01857031c825d,0x988b16d716964ad85817),(0xd5551dca9615ea159581,0xca40539354540153d494,0x5209c98a1d91d2529312,0x48d9d111519d09095cea,0xa9c8a988695c5c2ad0dd,0x7689b879907d08827dc,0x9bc028072850599028e9,0xfe66726e6a74646c6a7),(0xc0e52524244f8f64e4a6,0x62e300a2a24f2aa5a565,0xe1460e6123cee3810ea3,0x5945a205d8cdce0da1a1,0x8460cd1b5b05608504cd,0x4c206003dfc40c8ceb04,0xc31e5e0b5e8b838bc34c,0x5f9a9a5a02825edf02da),(0x30a1be50c573f016821f,0x5ea8890328078a142f0,0x2348ca143c011542851,0x5b25122d8052a33068ef,0x28517546d500a5307126,0xb81544d5139db751be6,0xec03a8350add5050a278,0xc01aaa58d99d2a2a16b9)),
((0x326100600002f80388b,0xa9e3006c39b34650dfaa,0xf5f3a0001c0e1ef80018,0xa33e034a2b200380d550,0x749b8711200366c2a4f5,0xe5c47d6b003800ae586e,0x24900e89d30c29cd025,0xa664508b970b15a3bf9f),(0x1cf4b57151ac4082d0ba,0xc099e810201280c4c29,0x200221e01b4091394100,0x28d42820030070196028,0xeb33c05040838a66293,0x2e712881bc5c0380070,0x605002000100003540c2,0x88ac30c8224600000200),(0x256a46600210e26080ae,0xb501cc84ad4c035c07c,0xa0945c1400000c282219,0x8d2d1a48f0c116c54271,0xc761417a8224545290c0,0xf0cb900fdf00006ce1f3,0x4900745dd9600e001a30,0x496e4083665309942a4),(0xe62306ad1ed59b400c0,0xc10a448090bc5ae56280,0x4c081844ea83a80c002a,0x330000343775281,0x2c00000000000000,0xc000200026642442aaa8,7177611906236893,0x7a67cf9d000c00108140),(0x4c8eb69b90d72a01d94e,0x51565c719820964b2a2a,0x20500d149312052885,0x5c01401c92c300004300,0x2c000000000300034000,0x24000002800000000000,0x100001c00002020000,0x404400008000000d518),(0,0x6d02bb0bb40000000000,0x50000269c0a4a2aaa680,0x1f02126386296502492,0x1900075c6dd02078881f,0x65800005c01c001a0006,0x1120000135150004c500,0x8c0000004033ce00d440),(51540131840,0x8280000000001d400000,0x200002c00000100001,0x300000000000000240,0xe070c418240000000740,0xfa54092a1ad8d214c073,0x7ae7a09eb268c17d3344,0x7cb21b7d35273d36e39e),(0xaecb2baaec2db6f17120,0x25965923a68a279a89ab,0xd7df79f79f8a08620e01,0x4985d65965596da6dc71,0x4a44f40f40d3945144c0,46280864,0,0x28000000006340143b00)),
((0xd229c28b6da000280050,0x140740005b69d8002,759171629,181390540800,0x38280b9b44a000000000,16,0x7d16dc38802e57000000,0x6e5c418506ec0b555fd3),(0x616495ad9eb778d5d347,0xd529a89a63266b98315f,0xfa33c8512094aeca89a9,0x19371ce482e68c24a094,0x62a508d1244098f1c76b,0x8c3460ba4284ce0c2039,0x7bde8000167cb0210182,0xf9bdf37cdef9defbbdef),(0x337bdefad6b5ad6b5ad6,0x655b4e749ce949e337ce,0x5ec731cd6c2128ca318c,0xa62a94a4a16a4a90c7b,0x110c4208c453188439,14416,0,19390494690648),(0,0,0,0,0x1808d6e0000000000000,0,0,0),(0xc0200000000000000000,1,0,0,0x200000000000000,0,0xe4422be8000000000000,0x8ada69e00044ba),(62915512,0x10000000000000000000,0x191d3f802d004d1ecdc,3448456085504,0,0xc980003cc801b179b998,12616466434,0),(0xabb380221a4c3d95800,0x650074f95312c3,941097152,0x4aa00291618bf32b9000,0x11b1a9ba88002b2abd4,0xf0d8000000,0xbb33274a3cca8042800,0x240d328c803a812cb279),(932385860354053,0x306923a4890148000000,0x152b8800025a649a4491,0x3e07ce1736801a829,0x439a3a4c02f830000000,0x6d100214604a1d1c7003,0x4f0d03b480004ed3a31,0xfc7c3c6a500000000000)),
((0x5d0c537459f0ea08fb79,0x20100000000009c20300,0xcc238000000000000000,0x385430e0000001dc18,0xb893583b6138b09941c8,0x280000a00000000000a8,0x2020000aa202222,0x2a020222200000000000),(2097154,0x20002a82283aa200,0x28022a20000000000000,9162597178,0x2a220422220223220000,0x3a2a2000000002000002,0x20000032a2283c2922,0x200321a8023028000000),(0xaaba2800002002002322,0xa20002a22202a3a28033,0x30aa2a2a322020000000,0x20000000220000220222,0x20232222002a20002aa2,0x30a0304a000000000082,0x31ae82b552002fb1,3407872),(0x194f8000000000000000,0x332d48ad94002f07ae,14231131008,0x2b800000000000000000,0x2acf1bc4b6844e2c9a2c,0,0x3a000000000000000000,0x29c83b8428ceab1a8100),(0x9329004d300072a,33554432,0x16008a529711c7a0a91b,0xfa6a7d18038a83d3e,0,0x1ec049951e4345800000,0x33b98e1d0000262717a1,0),(0x83939c34948446000000,0x9843ac20008c525bf1c,20786,0xcd4dc6c4159354000000,0xa40d8024929825114119,0x3900003b0047123c,0x86c1bed0b80000000000,0x988023882305428037c3),(0xc0bb5b7000022168d10,0xc0cc0406000000000000,0x481cb21cba28f0cccbf,0x801d8ec90005ca8b1f9f,0x220000000363c00000a,9294577714,0x2222203232a000000000,2097664),(3859028257312,0xa2024222020000000000,0x2000002a2020242,0x2302022332a202282220,0x2002a000000000000000,2929704739488,0x2003328210202020000,0xa22a2200000000000022)))

def page3 : WordPage :=
(((0x200200aa2201c0228a2,0x2133302032302000000,0x22200000002a2002b3aa,0x21802a31b022ab322002,0xddec73e9c80000000020,0x52cd7b9d6dfab5e6af8e,0x38cddd276cfde0004ead,0x3e6879a970a32e653954),(0xc2cf072e88ba646c0002,0x40071d800068044d51b5,0x79ebc007df9d7c6e06,0x4df18030eb0b9bc0005f,0x4c9970465c600000036c,0x4b33000001468c9a8060,0x72a52a142d00a00002ac,0x9256000115f7400000b1),(0x51e98000000060000006,3932042559618,39926016168323,0x1c080000000000004240,0x4600011105421900000,0x8f2472491c71c9246000,0x10befbef80000000f811,0xe00000000045042fbefc),(0xdb8eb6f36000038e36,0xc34c00c300000000000,0x2cb80000000b00cb200,0x32e000000bacb80,0xa2aa2800000280000000,0x9a020000000000000,0x888000920000,0x79c00001c71c0000000),(0x58000061600000000,107479040,0xdb6c9301125124020000,0x79828cc0370277750dec,0x525a7e5802a538f5b0a4,0xa890f50d32200003a9a1,0x858d1eae1743132dd4b1,0x5651cb25ea819504fa62),(0x81d9761c1979c7416703,0x803c1ace4d80228fa51,0x23eb6a2e75cf157822cc,0x43764c3491a77b8f9f6a,0x2a997a1fdbcdba09dca4,0x728563ae7c556332119b,0x6fa54d8f857d07ce0003,0xda24a1ab0e3594123f04),(0x528096f31086c6836859,0xb084845415c081b4f9e2,0xda1aa38e889800005a89,0x11ad41c5e5e3aaa0039a,0xc8ae5ac0254b1e602739,0x6340427278edb2275823,0x9d86be428f427782808d,0x6d670eae0881a55ccf03),(0x758d9bc94f0cb50c8a08,0xbf44bb1d5715fe354c4a,0x9e5ae96ecdb916e0b321,0x217b149ca6b6dcad4e7a,0x94a2b20734d1a3a553b2,0xa84475e4528cfdc7c4d1,0x3000055216b80493ce93,0x318e94e836b70c3cc99a)),
((0xca6a2621eb6a2f8de7b1,0x84b04e00355db0b0e822,0x20b9155c3368c96e7acc,0x28a067c4d6ca4e2815f8,0x9b8729bb56a48a00d728,0x8d35e7cebbfe59973ee6,0x4b8625c212e0c7648f3c,0xb16359721ca3a2b09760),(0x1a515490af34c79e824e,0x896744b0e500f39859f0,0xc0484e90de5e7d84e194,0x78404833389358800013,0xf9cd69b2e8c1702e19b3,0xa1688250f96a920fa18c,0x1387ea62a22f41846af0,0xb2e65933188ee18c89c1),(0x452b8c322519921f2e3,0x8a2b6110016e818c19c0,0x1a6ba1ea1211e1074a89,0xc945b2d1512912305145,0x58d220eb09b288c6a2ad,0xfb353ce4028284ed7472,0x48def9800161e5f480b,0xe51e028c9984b6cd98a9),(0xd28d232a007400129550,0x66b4c162326c1dad41e7,0x765d69d8f1735800f2d8,0x94a657a1ce9adce5d16e,0x88ea8ab6c691919389ca,0x8fa0fa52dc6669eb7dc2,0x328da00a0205a2aba,0xcba5448a442c41ce1caa),(0x44f946a4c9a143c33c12,0x41a854b3336339309c9d,0xf291ba938e4154194005,0x581ffdb1f077a1f2b033,0x4ecd1061990291676500,0x570d0f0a6f8a676914b3,0xf4a30436c6edee7d4018,0x698a9cb8b2a095865c42),(0xf478731c351582d46754,0xa8ac02d026000c990082,0xb272dc9bc848b9155714,0xc7a3e6d1d6b0c3113924,0xc6030c1dd38318d640,0xf65ae300310191b73672,0xe66b19027e859d15a88b,0x11f9d498b78f00311ba1),(0x770b6d17a1d96c48b5f2,0xb4720939e09bf7463d96,0xb2a54a7ffce43ac32017,0xf16fc85d5bdd571d7d25,0x973b7ec56ec87bd000be,0xdc84b1eb8966d6809e9,0xc07565ca6916286ca79d,0x44faa17d70a5e1bc8078),(0x40c2e0bd4fca0fe985ec,0x1a94be5331cce9e25bc2,0x91cbab221e65cc98ed7f,0x58ce7f4a9291167368f1,0x3d0c000c2cb96afd4b44,0x2914b4aaab53d6882b61,0xa8509ab025a2e5ac616e,0x7890fa3095a69f63194b)),
((0x664bd489894a8a474af3,0x65505336f91064fdce43,0x3fa2168327c60b5d8bc3,0xd746f4a2671273d13f1c,0x88dd5c699416112bd089,0x4ab597e085e96378717a,0xe072be2079a096849354,0x8a37cf099825df45cbe4),(0xc8aaa5d602e7c99e744e,0x1de059da64a2365103b5,0xfe95b1c8e7e349537679,0x92b858f7cca9c267391a,0x2f331be087f3429106de,0xf7c1f99129f97528bee6,0x107bbe56b7229a17afc8,0x7cb46d5e479513dd87c),(0xb7e8ef7108147cd533dc,0xc71fd9e571979887271,0x20a175e9497db85f6a19,0x8506a5d529de21bd874e,0x9642c904e5127778fa9c,0x887478bb96526f532c8d,0x3689971ecd8f6179113c,0x5c12a22058fc97d87c6e),(0x9265b72a1b1c80178887,0x1a75885ad298f2474189,0xf0a0eed22b0c48d3b04a,0xe2608000a2019be4b170,0x32050b9cc0635129d98f,0xb9968cba631b98d0c666,0x773a522a186f0374a722,0x650b2c59824e302a944d),(0x5922b59db8ee277436b1,0x9600b185105c71171f20,0x8c26984a898c4c4001bd,0x29a39a08b424a325a0d2,0x10c1d90053fd4aae552b,0x4133e96708fa39f2588d,0xab875f3c314d131058a2,0x394a4b525a47c6ac9e10),(0x8aac670692a139cecc48,0x50a4bd8e188f557a9e0,0x2cc8eede571ab78dd4af,0x1d490a3515b2ad946a18,0x3b88ba3194bf954cf363,0x55018aa6686fa43e1353,0x2a64d302cf517c0bc6f4,0x930c5805e14180ac5565),(0xa5b5a63c000a8d6998c6,0xb302928994f6320407ad,0x38d20b896802a1a681a,0x595348eb5cd04b562f20,0x2d876b68a21cf480a365,0x700054d4200910b2d099,0x8914a393752532496325,0x248d1bf364a760054237),(0x8dc4b58ad416ca000132,0xbd5410ac19ba5d276d7c,0x5328ea986c00980b0091,0x6453b6971be91a4e8003,0x310a2ae8815892cb59d,0x28c4f704045c84470402,0x58702c88d5d0b41002c6,0xb8ae14923398d9159293)),
((0x68f61215d304408b0a03,0x42717923218132520900,0x12b33b63396000046169,0x39d1894585ae34f2b12d,0x531a53cf2a833360b1ab,0x31cb24a1854535532cd2,0x2a23a212d62d1c32c92c,0x2767947d48145e2451bc),(0x149f34e5216138b02754,0x100a993c729c39c20a97,0xd514956d41b6c5296396,0xe2c02654d41c22933694,0x48d3445903b92bb2bb1b,0xb400913f55d4d3123161,0xf324d45565d865142069,0x8b37209213b22e940001),(0x53323d0ef425206de446,0x9c54b2b251472f22c1,0x71b9a34790de875c40a,0x53ecd421949c7b604e26,0xc18a9c548c927242caa6,0x352d644fc71f22494ed3,0x40544404ae63b1130723,0x8b983268d90a080e1d3c),(0xbdaf5192d4c9848000a5,0xad803090d41d444f1404,0x89a5695252a1a8402004,0xec96659196719c47dbf4,0x41354dd136e5132ed3d4,0xc00e42d8b42188414906,0xd2d62d5ca27a0e0c5923,0xe7ee4d71f802526800a4),(0x343296d8014317551c51,0x96e567591ba890f8ab1,0x1858f92b209994b92af,0xd4d46950c0ef4adc9004,0x44c65c771000bcb91b4,0xa98a5a94b61a6691a301,0xca7295074dd674d5974c,0xa18856749648735c8494),(0x8558d1d8759d59509222,0xc270961402c571500215,0x156e1df4663b6ed3e664,0x386100d8358d4d591856,0x1640050c168f8a10149b,0x432000058acccb941718,0x864aa988ccb3958dd048,0x5866a571e0d43d20fc82),(0x9f8502ece481728ec86a,0x4e7555cdc824e400b14a,0xe57cd545768d8d481229,0x50d299d60fa93774f9de,0x77d620382519367915e9,0xc1dd056359d550aa9da5,0x52053489dcb508292974,0xa1d346dd1b261d987381),(0x148b49c6522a61a3605,0xc88a497b605a9bf58aca,0x620651476e954b385ccc,0x26d8bc81e64c48661575,0xa096a66d157066e0a143,0x8a1137f51c331c25af58,0x3d4b5756496362610089,0x2726257e333231863f3e)),
((0x76758d0302010f1b1a0d,0x84da80064b419b006e6d,0xd218104410539acb515,0xe00008d1c406436a1022,0xd1756c45f83094c903c2,0xc003b75ca000400036a4,0x790074a912e14c09f68c,0x78e875c8f8f478209149),(0x9590f81095ace41ed11d,0xb7f0864e6e99b674d800,0x46026e65b574f65cd748,0x740532b958dc6476a123,0x529145b667de58c478d0,0xd644c18b30f16e31b950,0xd734b3e137e08366f62c,0x70c567964d29d9485614),(0x194057d088f22f8d98b8,0x3938548918ac68ae2a36,0xe9f619304b91ebcde86a,0xb3bd3269474e5558eb55,0x8dfdb2414f5d95fcd720,0xd7b097c080bb5099651a,0xb7a098a07520f53cecf1,0xb70c506d78946b19edc9),(0x7888624f0a75eab1f70c,0x7041795839285870787c,0x301578647504f790856a,0x79185858792053753399,0x391059084cb9cd95b84c,0x17808d61b32d35e4d351,0xa4ca8c81d84076f8a1ef,0xa2aee826230aefe976e4),(0x46f65469130928d456d0,0xfbd71f146ae56bcb219,0xeefd977094290f2d9449,0x497611a151c949b614e8,0xa694cae98ecd89360464,0x62bd8325a800724738,0xaa84969912439de3a400,0x2c920800040206401dba),(0xaa202130b68215df257c,0x965f1a6218924576adb5,0x16aa0db0a8e8baab8e7f,0x8e78167a94c8bd2a367d,0xbc89c4c13da9aaa70ea8,0x1a9712b5880e6ca2c0b9,0x3e391e7596591a3c9e5c,0xa6a58eb4891d3523b4b2),(0x22a40e321dd626359dda,0xaa931295121821a4aa1c,0x2195a99aa8814672159f,0x5c65cd90aa1021712e14,0xa4e1ba91120c2116b433,0xb58ba9103478485c4dd1,0x34007027de0820000909,0xb4aabdcd266f956bad03),(0x1186a955309ac1662cfc,0x32042052ce561a2e9e8f,0x8aa28dfc21493200214f,0x14d01e9f8e508aa10eb3,0xa5c88a9e0e531a8d126d,0x8df821f80a2b1eb289c8,0xac1be01b88494e8b129c,0x326a96b18a4d1a501960)),
((0x22af886f4ab08981a943,0x8aae883ed64a19f021f4,0x25ec22471a89126816ad,0x353d329b0e8712ac89c4,0x153732279de820dab8f6,0xa241cd3b95b2cefb665,0x89bfa5ae16740c0a8667,0x6ca482b684cf8c6d8638),(0xd0853d9ad020000c4f70,0xea645d4f070ca99730f2,0x4a2064ae8200c1eb0a2c,0xea990c4302ab14f29a41,0x268af8ee6b4e46315b06,0x79adcee3b229127a2eae,0xb4968b03a190b3bb82d3,0xa09040d5044408cd86dd),(0x7e83189f9121a48e8acb,0x52dab46e8a93c00b1da4,0x740109821a627cc2bd98,0xde83643bd1732d7b099,0xdabf665849e913499604,0xb352c4f494f20074668f,0x9c9076401daceb45e8d1,0xe2ac8b32ed2e992b2fb2),(0xc61e0a022f3aa96ef62b,0x33f14c669c3a88ea214c,0x98b85181413c4af11038,0xeac4e915a4c0691ba54e,0x38db4ec2cb672d91b90e,0xa006a43a6b11a44668e,0x92aeacaa2c3c4c5cdd0c,0x54531c6664627e7ae496),(0x21e1cd41af504f24442,0x43001184003432c40604,0x75544d244f38b2892071,0xc01411238a181f75b65,0xd75955123cd30a2481c6,0x30050449648e28607dc6,0x61759440f38b28920718,0xc00441669238607dd719),(0x17da61759238a2481c60,0x38d2c91c60c20050448e,0x70401851207de71b58f,0x642850c10061222892,0xa090807060504030201,0x1817131211100f0e0d0b,0x24232221201f1e1d1c1b,0x363534302e2d2b2a2726),(0x44403f3e3d3c3b3a3938,0x5e5c5958555451474645,0x7675726f6e6a6561605f,0x8f8e8c8b838281807d78,0x6050403010200649190,0x1312110f0e0d0c0b0a08,0x252322211f1d1c1a1917,0x3d3c37312f2e2b2a2726),(0x4a49484645444342413f,0x6562605b5a5957554d4b,0x88878677747371706a67,0x2006491908f8d8c8b89,0xb0a0908070605040301,0x1a19151211100f0e0d0c,0x32302e2a2622211e1c1b,0x423f3c3a393836353433)),
((0x5956545352504f4e4c43,0x7c7b7a796d65605e5b5a,0x8f8c8b8a868583807f7e,0x8050403010002649190,0x14131211100f0d0c0a09,0x43423f3e30292826231c,0x5e5c5b57554a49484645,0x89888574716a69686561),(0x504030165008e8d8c8b,0x221f1b16150e0d0a0906,0x3736302c2b2a27262423,0x5c5b5654524543413c39,0x8f8c8a847e66645f5e5d,0x9050301001064029190,0x392f261312110f0e0c0b,0x8774716c6b6765635241),(0x9080706010064028d8b,0x56391d1211100f0e0c0b,0x810060200e24018b8f69,0x803c1c0b050240e0602,0x3d1e0ec70371a8502611,0xac552a148a2502791c8c,0x45cad968b419ec561b08,0x2602ff7dbb556a953a95),(0x30100401b50272753a7c,0x614068301609040180a0,0xaed455d2c5601e0e8703,0x6ef75b8dbedb6999c35f,0x30140803010041c00c6,0x12088401e0d060281007,0xc4612b9389a4b2485026,0x7dbcdd6e1acd4693419c),(0xcd6eb4e97439dcce1703,0x2d9f274b8ac2e13017bb,0xa0c0401c0c0502004001,0x48a44219082210078381,0xecb63b0c6611b0d76b35,0x10040146a3e1b79b6da,0xb050241007030140803,0x44211007c28130703418),(0xcd64391c0c862301788c,0xf5eef37660b017ebe5a2,0xc5f2755a7d268f1180b,0xe0e058280c0401004001,0x578bb170b4582b0a0441,0xeeb71b7d7e6b1385c22f,0x180802000804717bcdd,0xf0702c1409040180a04),(0x8c381b8d86a341985026,0x218ec662b1186c22411c,0x6270b84a9545b6da64b,0x10003405c9d56a74fa6d,0x2b0578a8381a0a030120,0xf75b6dae230d80a2ae97,0xc000200e238dc4e0ee,0x78381a0c05828120502),(0xa04ea713014098482210,0x5d299449d4ea551a8942,0x5b1f8ac3dba7539984be,0x200c036a0000b399bcbe,0x309044200e0602810070,0x51f8ec72369d47230281,0x26933994b6592a9248e4,0x6371585c15fadb6bb4da)),
((0x3014080300800055ac0,0x110803c1c0d060281007,0xdc6d351a4b2580a04c24,0xaf778adbe9f2e7731bc,0x30080200096331385c26,0x2088401e0e0683010070,0x4e16f374c24c251248a4,0xb438bc5617017979b8dc),(0x400100972779b6d8e8,0xc0c3a1a8240a00220501,0x155373b7db6b7598a,0x160a0481c0c050200c02,0x44803d0a04c221007838,0x233d9ccd2e16cb453291,0x9c25f6ed59ac55eab537,0xa0401808034ba4803178),(0xc1c0d0602c1208038180,0x8e85228138984a240a04,0xbc5da95486632d94b65a,0xa5771187c3602f779,0x1a0c038180a040180802,0xc0bc5d09848221007838,0xf571e0ef773b4e672389,0xcc36170982c05eec15fa),(0x80a03014080200800238,0xcc653204c200f070341,0x6370982be5e5f0f77a1d,0x1004014da66ef67a5d1,0xb050241007030140803,0x6cb5208fc7c140703418,0x3e9d4ba552690cb5c2dd,0x5822fd7bbcde2ef76a85),(0xd0481c080301004000c0,0x489419d8ea14098441c0,0x6210f8341609038122d1,0x80385c9cfe43198abe44,0xc360432180b8582a0d00,0x110971f8dc5e270f8388,0x2810070280e020080314,0x562913892210e8642a10),(0xa64f2591c4616f5268b4,0x10002b6fc9d467b3b95c,0x61308034180b02810040,0x8038ac600375abc44952,0x83016090401c0c040180,0x3d8502612088401e0e06,0x648d466311785425208f,0xc0501802f602e4e3b01),(0x32f15dae3b8e40e0681c,0x38180a0200e202200e3e,0xc0a04c2410078381a0c0,0x11e8a4493a9b4d2651a8,0xb4d8ac3dfad36895c864,0x8180a04018080200b5da,0x80381a0c05828120803,0x6c994c6469f4f0502411),(0x18c0102b1588c15fadb,0x381a0c048180a0401804,0xd1e4d814098482210078,0x9c058611077ebf1f67c3,0xe06010040188ce61f178,0x2612088401a0c058280,0xca651275125d2c954a05,0x63015c9d366f2d8f9b)))

def page4 : WordPage :=
(((0x85bcbc9e2140803c1201,0x60200d600156ddee367,0x401c0a048200e0602810,0x63add4d469b48c05f0a0,0xb862f1385c25dab3577,0x40903814080301004280,0x2612088401e0d0602c1,0xe0b0172b8dbe6d3554aa),(0x18080200030101588c3,0x1409844200f070341205,0xecf57a1e0ee7433190c6,0x10060803f274589c23dd,0x2eef6daec6400180b048,0x8038180803008002802b,0x612088401e0d0602c120,0xb0167b34312491479fc2),(0xc04010002b0e0bc662,0x90441a0c0481c0c0502,0x399c4be5ca7532902813,0x401007269996c05f2dd,0x501c0d060240e060200c,0x2dfaf176a853e9d4d5b8,0x2008002962e3f178986c,0xc0d06028120602810060),(0x2c6ff7f1f824110803c1,0x8100200c380b1b8cc4e0,0x78381a0b050200e0602,0x859ecf276ab550502210,0x200e0582810060204805,0x270198a0d027eac0a04c,0x58240c050200c0400b17,0xcc4df2c70b7f0501e0c0),(0x8090200c0166015978f8,0x2fb0c491f42812080341,0x441801df03b93c4c560,0x340602e470f81bfc6,0x12088401e0e060240e05,0x1e0206e0f03445705026,0xb42813090441c0c05000,0x70440591c1e06eb43a12),(0xf0682c14070301408000,0x4090440585b9850200,0xe7c14098401c0c058241,0x8240e0602dc30002cc60,0x300c0802be5c66a0c05,0x207e0ee814098381608,0x19c9c184c22100703702,0x202610ddc06000f00033),(0x5008020f09038160a010,0x6e20002001e4e7c220d0,0x1c9c28401c0b0301405c,0x1608078380010dee2c0,0x8280e0401801f6050084,0x2d14c6c31130881e0e06,0xef773b4e26f3418cc45b,0x2510803f9fafc79bc9e0),(0x8ec3609047e3b1b8d44e,0x1dfafb7bbd5d6e772b75,0x1000080805fbfd3c384c,0x65a2c94c380f07034100,0xde6e34998c46130174b,0xab1568b42a09007d389c,0xb9dc2df64b057d60af56,0xe5f1763a97ebe5deed74)),
((0x201d67f3f5f77abd1,0x441e0e0681c0c0502004,0x61c4c2602d968b01b098,0xc4d265269248a411e8d4,0xebb5d2e570b75b2d5669,0xae76fb3596c960afd757,0x4015d01817f37ebe5d,0xf8681e0e06828100702),(0x71361acd4642a950a627,0x9ccd6632590b1552a148,0xdaeb74b95c2d5676ab51,0x5f9bc9e3f061b017dbd5,0xb04004000202017f1f7f,0x85d2c0642e12078381a0,0x8ea74389b0d66a3419cc,0x57ab8984ba592a943c1d),(0xbd5e2eb74b95badb6bb3,0x4f9fcbd9eaf3f7efd7d,0x1e0e0682c1001000080a,0xb8d66a3218cbe5b2d160,0x733596ca64b1d4ca4519,0xfbedeeed75b95c2d5676,0xbbfdf6f775b9d86bf5d7,0x4000301017efedf5f9ba),(0x160ac0f0703410070200,0x41a090280389b8d0612d,0xaf572b51c8d45a190a84,0xdf65b2582bf5d5d2d160,0x6bedf2f8fbafd7cbd5da,0x6818080301004015b7dd,0xc7d1c0c65a1e0984a0f0,0xb1c8dc220f007fbf9faf),(0x6d165b0d824d218fc7a3,0x8000403b0dd6e76fb65a,0x2a9504e0f070340e0500,0xaf552a550a73898cae56,0xc75d6c35dacd56a34d62,0xe3017fbedeeeb74b85aa,0x7034180601000100103f,0x53f1f4de6631180b80f0),(0x185bf5f2f377b9dbd4ca,0x397c7e270b81b4d5e9b4,0x8301002008180007e6f3,0x3518cc45f2e1681e0e06,0x7bbab0d84c1511b8da6b,0x77bad96c755a9d267efb,0x80200024480bcde2eff,0x194c8037078381a0b040),(0x388c3de2f077bb8e0663,0xdd3e560afb7bbadceb71,0x400050100feff4f876ba,0x1702c15078381a0a0380,0x3e1ecf4793b9c4d46832,0x66af572b75a50a813e94,0x17ba3df6f574b95c2dd,0x8e9348a3184740d01808),(0x60200e0100018e467b2d,0x3359a8cc632e83c1c0d0,0xb7ebedeaeb5e452250e7,0x38fc6e270f71b6da6cb5,0x341002008000ae30272,0x3599cc256180a8520f07,0x6a72389c2e0621c4de6e,0xdfebf4f8fbd7dbddcee5)),
((0x200e05018080204b7803,0x178a853208f83c1d068,0xc95ca651278b456290c3,0x9e8bf5e6e771b6d8e652,0x41e0e068200200010140,0xbd1bede6e1b8d8662d16,0xc0de6ef71b7be5f0f67a,0xb78100bf7ee75fa1ce),(0xbc390f0381a0b0400802,0xd2fd2c954a61b0c859b8,0x1f6fb3d2e8f3f91bcdbe,0xc0803414070080004050,0xf77439dcce5709c45c2,0x2f377b8da6c50280be5f,0x808020062d840781bf5f,0x631c4d02f168381a0702),(0x75763add4e969345a0cf,0x5b7d8bef7dbddeaf1,0x38a83e118381a0301004,0xa4ce65318cc622f168ac,0xfb156efd79b9dc6db689,0x60f070340a0401804015,0xe02e773384e25a190b05,0x812b579bbdc6d9058240),(0x78381a090300c040000,0x5cacb6db4be5eaf16414,0x55abedd6e970b5586bb,0x841a0903010060100564,0xc4de4722389807633120,0xe03dfaeb71b7da2c5609,0xe0d060200c0200803800,0x21509379acd466329881),(0x81395bfd9ea347a1bd59,0x7034160803818020002,0x7270b74e26b33180b828,0xc5cce17076bacbdde2e7,0x248e38068140200b280a,0xc55e974aa451cba50269,0x107de6eb73b8db6c761a,0x65d07030100701001100),(0x6fd76b95bacc8a369b0d,0x572b3c9e4673379acae4,0x68240c050200c020001,0x5a5027d3c7b2e0601e0e,0x15f02576f572b5d92bd,0x60360f07034120601804,0x2582b2c05fa75389b389,0x501804016b015b6f976b),(0xd2d38998c05b260801e0,0x57dbd5dee341984be5,0xfc78340703402000181,0xb0d82b52692c92110783,0x9010001e01badced968,0x177c3f9accc5d0602c14,0xfad39bcb64f218fc7633,0xd1c4a44a2401c0a029e5),(0x6b9d8a9d4da04fa7b3b9,0xc63070200e020003c0d7,0x55be4f1f4b9ebd9a4c,0x83c1c0d0481806010001,0x15f6f778b7586bceb67,0x3f389449e421a802cf5c,0xe370b4d8abb55a7d3287,0x3896442180c016baf57e)),
((0x15b6d35da250a6d352d9,0x2a8d40e24d230e07b530,0x75abad96c762b0d72a95,0x8c20f05010060100572b,0x8001c070366b115eac9a,0xe670b6add07834100200,0xa2338341807008200c00,0xc0300810055fde6df4f),(0xc0361aed72c55b06824,0x24180acedd1b209020,0x101d7b2f94c6e2b0e0b0,0x20e0381af77807828036,0x48b60b380b3568050200,0x9733396008032562ab1c,0x17768b3902e60185905,0xee016df62b01b0cd6b),(0x9598c483c0a010281004,0xba2500601002002a0a5a,0xd6751d2741c2701be6f1,0xa2961e8799e4781dc761,0xe0b7adcb6ad4b4ac6aea,0xb2e4b8ad4b4ed2b48d02,0x6919c6518c5f173b6ed3,0xa6b8aa7c731bc6d1ac),(0x440e0360d03001804008,0x841904408ee3b0ea250,0x769aa68461104390c429,0xc0aeab8ad2a0a4a8aa0a,0xa0c3b0ac2306b7ad8b2a,0x4a7c110340b01402e8b,0x940c82c0a82800800018,0xe8398dc368d8358d4348),(0x63f8fc3e8f63d0f23b0,0xfab42c0a829a4310a421,0xfcfebf4e538ac1302c02,0x52bc0d02c0901c03003,0x941e8761c86c00800018,0xca721c6711b86d9b46c8,0x6a6c58e338ad0b3c731,0x501384c1284800800250),(0x384d9344c12e4b128498,0x4e5314a511425013e4f1,0x14c4aa29a1625815a541,0x1905c14e338ac7b1cc5b,0xace2caf2b4230841f074,0x9c268940400c02802004,0x8ee32eea70aa2a0a6278,0xe280675be0f7bdcf6b),(0xb66d0941f8781d874008,0xca719c4701be6f1ba6e1,0xe2779dc769d8751ce731,0x46d133eabaa2a828e999,0x6919c6518c6117c5b163,0x940700600800388052bc,0xfcb48e4380de338cc328,0x9b2b3f2fc3eee3b8ce2a),(0x3c250500180200004a8a,0x5e5715a56148519424f9,0xaaa2a849fa7c9c962581,0x1ac62e0b52cab1abeab2,0x9509c2508c2107b8ac83,0xd02500601002003b4a5a,0x789ba6c9925e7a1e6749,0xbaacaaeaa2a6a8aa0a12)),
((0x50d32e4b7adcb52d2b1a,0xae014731c46aedbb2d4b,0x421003e0f03a0080001c,0x2648920478941384c118,0x3a4e1364c92e4b12a4a1,0x14e338ac42905414e531,0xa60c0a741d06c1905c,0x94090200781801804008),(0xbc2d8b22c0ae2b0a2280,0x94a22729ba5c310c22f8,0xeafa3e6f8b8ce2af0a5a,0x822007c00800018052bb,0xfa7c1ee7b1ea25088218,0xaf1f476e338ad51fe7f1,0x8a21884208040080001c,0xf87d9f27c1ee7a894230),(0xa82206812007f9fc7e9,0x7b1e4771d38ad5ab0a92,0x600800a7baea5c831fc,0x606b9ac6a9a869198250,0xe2b62d0b12b2ac2a499a,0x8aceb38cdb34ccae8b9a,0xa46a45715451133b0e4b,0x941a062018040080065a),(0x9e6719a651906398c628,0xc8ac28c6c1ae6b1aa699,0x531444f1338acc2d6b42,0x5e16806008005b0052bc,0x28c9acc5c9705b96a250,0xae018050dc350cb8acab,0xd0328940b82a0a026004,0xf63c0e2380de368d8358),(0xfebe2a0a79003f8fa3e0,0xffbfafe3f6fc38ce2a,0x9401804008011f2a4824,0xe8320a81a047d9f47c8,0xd6b4ac8af2baabaa6a12,0x8ad735ad62e8b9ae2b7a,0x400800a73aaa5c811fb,0x5a62186609805f97c250),(0xceb32a2a027a9d266982,0x38eb3a8e4b2ecb2e4b82,0x200292a6295114430f4,0x66591565515225006010,0x88a127c9ca6c992545a1,0x28e9ba4e4b24c8aa2a6a,0xa6a9ea4c310bc2d0ac,0x18459144490225006008),(0x8aa0a769c26a9891c469,0x96e4b0cb42cab12b4a82,0x94a72930440ee8ba0e7b,0xc4300940880601002002,0x84a0a809e272958c8318,0xf6bd2ccadaaaa6296a1a,0x94f0bc4fb39ce6b98e2a,0x368ca308b00601002000),(0xbeac2aaa92a0a6a989ca,0x8addb74dcb70dbae8b4a,0x903c6f249d26c98f4b,0x3e8f23a8e09424804008,0xa4a8a4e9324891a4490a,0xa528ca127b82e037edf2,0x1200800a600401cad2a4,0xb62d0a4288a025016050)),
((0xecbaab6a72729c0ba2e0,0x8a01caef93e2e338abca,0x941a066190621800400b,0x48e31a26819c64990630,0x122400200094efbc112c,0x8c9fa2087a1c86216852,0x68d9b64b62cea7a9ca6a,0xef294eec93243d0dab),(0x849b2108089401804008,0x60b8ac8ac2aea92a0a4a,0x945fc8921c84f3bb8e4b,0x785d9740180400800a88,0xdcb1a90611826017c5e9,0xc8f1c410fc3d0ec38e2a,0x4e9324a25004008012a3,0x82b82dcb22a4a8a98942),(0xd2f0bc52abd4e2386e13,0x98a2a2a8a09401002003,0x72ba2caafab4a92a0a6a,0x4003aea5a9ede376dd3,0xc4ae2b2aa2a4a1a7a250,0x8f2bc57153ccec2d8b42,0x9a260960380601000253,0xacf6bd8f5b90e338aa70),(0x9a8821c25004a7bc0efc,0x66b62ceb32cab12b6a72,0x5615000250072bc90f43,0xad0db8c5c16c1705a160,0x769c26a25004a7294a4c,0x92b32a8a9a98a5a84a0a,0x6e1b06a018052bb9ce6b,0x30254952b38c949b21c0),(0x348ca2e8b2248880400a,0x52bc96e2b6cb5aa48da,0xad04b8c490400e800018,0xa8a8a8661800a7296eac,0xaef2bacb3accb0ab6aca,0x4254ace30520000401c,0x16850902380600800860,0x98a548f2348ae2a8c86a),(0xbea9aa2a6a92018052ba,0x4e28950b42ae9ba4b2a,0x9edeaa490a408f802000,0xd825806020052bca7284,0xa6a9292a0adea82952b3,0x201caf21bceef35eb6a,0xaf2b094018052ba26250,0xaed8806014ae0100711c),(0x805d67e201b2bb8a014,0xc9c1b1a981493128a810,0xbbb37b6b6353227261d1,0xe6d6ae96160dedb5a3c3,0x81507068401008067db5,0x5209f1e1d9b9b1a19989,0x7e060eceb5c5a57b7b73,0x2a19c971689820100806),(0xd59d83a38b53433a4a3a,0x635b5261c9c010067ded,0x2808001625f5b5a3736b,0x7b526a31d1b1a9796948,0x38100805e6060bc3bbb3,0x9b938b6a01d191716949,0x5ee7d6eb67dd5cbdba3,0x733aca9a41d1c9181008)),
((0x7e3e1604d4ccc3d39b7b,0xd39ac2a9a0e010080636,0x856e7ec6a66e6643e3db,0xb6b632a522210780805,0xf60e05e5943c342c2414,0xd56e7e05e5ab600801d5,0x544bdbbbb1c818100805,0x7e36d625f5ede46c645c),(0xa2918108f8801008063e,0x85e6665615dbbbb3aab2,0x6b635a50a0901008067d,0xe67d6dbc3c342c1c138b,0x260cf4eb9af2e8100804,0x804b56e7eb6a6463e36,0x2e05fdecd4ccc4bb71d0,0xb988d8c8b01003de3e36),(0x66363eceae55ebd3a381,0x99a9a181694058100806,0xe28008052d356bbbb3ab,0x6e7e3e35453d238b1b12,0x34aca49c9258100805ed,0x7e363ebe7bd3c950063e,0xe3db32dad2b8c0100806,0xe088100803d3de36b64b),(0x5767de6c6a6663958e8,0x9371f9e9b9b1a0504810,0x150d02fa8808067cfd6d,0x792005656d5ea63e351d,0x5b56e7e563e35554baa,0x114e31969e25e5a44378,0x36ce3debbbb331716860,0x8e5bd39ac100f005ee06),(0x9b71b9816005b67de6b6,0x38100805767db5a58d73,0x8067d256da59403fb48,0x7e1e36c6b6353d352b18,0x66863de3c3b150100806,0x5e7d6eceb6a67e738803,0x7d6e3565554bd3081005,0x7e361c8c847998080476),(0xe61de5b593f3e805756e,0x6363eb3a1c8b81000d5,0x900ded6e7ec6a3630110,0x6e7decd806056e7caca4,0xc9b148136624847c75e5,0xa33035f6362d1d150d01,0xa996ceb6a006c6a99815,0x70686048402019a80801),(0xc0b8b0a8a09890888078,0x2119110900f8e0d8d0c8,0xc9c1a199914941393129,0x4a42322a1a1201f9f1e9,0xaaa2928a827a72625a52,0xfaf2eae2dad2cac2bab2,0x44341c140c03ebe3dbd2,0x78583830281811880804),(0xc8c0b8b0a8a098908880,0x49413931292118e0d8d0,0xb1a99981797169615951,0xb2aaa29a928a726a61c1,0x231b12f2eae2d2cac2ba,0x837b736b635b53433b33,0xc4c2c23e3cbc3ab93,0x60585048403830281170)),
((0x7969615950e0b0787068,0x332b231b130b01c1b181,0x837b736b635b534b433b,0xfbf3cbbbb3aba39b938b,0x602108080474645c542b,0xf8f0e8e0b090887870,0xa01f1e9e1d9d1b9a111,0x6c3be3d23a322a221a12),(0x16284070c14201040c04,0xa6cd182e54a12223c70c,0xc172b54a54244280f9e3,0x69cf9d361c180f5c3768,0x60b14244070c04280b15,0xa5488901e3664c15243c,0x58909e3660b15aa52a13,0x224057ad4a6cc93223c),(0xc9519c32589901a3058a,0x2e5467cedd395eb96a84,0x8407080418201529d1a1,0x5aa5284f9d345ca11182,0x40806913f6acd93160b9,0x21fbb8b5272839a8398a,0x310737a460f698a4080e,0x985fe6ab47b9a62900),(0xe694821803cb51cd2906,0x27e916a040184ffdd1e,0x94286262cc0189cd1844,0x2892070816a1012500c4,0x2389b6585d651340f30b,0x81820408a1f7bd74be9a,0xdb1b235544d238d30b24,0xce34c2481c51018a103a),(0x308186203ce73ae34503,0x878df2ba334c2481c510,0x975954d245034c04063c,0x62481030810225f5b638,0x2481c4021eb9eea8e161,0x9d70a2006c9de7922713,0x7143081034c21ef89a17,0x87c9606cc021f5f88a24),(0x105ff70831ff7b884797,0x20827f08293fd420b7ec,0xe6840cf38207f9e1043d,0xcff20d7d4102fcb0819,0xa078206f820a7c20afc2,0xf406027485074c02f42,0xd00fa03f40ef6c1f07a2,0x2727fce9d1fdf020e805),(0x1840026bed9e60a2000a,0x34b92184002694f34592,0x681c00c0a680e300a829,0x806087cd03a0806087c,0x941bcd2e68008652270a,0xe6942001980bcd2e6800,0xeb278860322a80008e91,0xb80806925c440e080b40),(0xc0b04801025ca4801025,0x2209cb10002a50400a2,0x1648200290f0a098c08a,0x6a1090c0a408f3a22821,0x265a91da846548ef5447,0xf6e5d4c32a10b819a3b2,0x304000f6e5d4c3b20a81,0x203c68b14244070c1420)))

def page5 : WordPage :=
(((0x2bd72c56a5426386cc96,0x1fbe78e5c376cd5a336,0x868c54000cb911e24385,0xf9e3a68c172a50992223,0xb05ab13a64a911a24280,0xa932234582f5e3b74c98,0x1f81ffb4720c4082f1d4,0x64f60c20dfb759312708),(0x402b66706a8a100adcc5,0xf7fd5e9172020e926d50,0x22e083fa2564f62420c0,0x22b075c4feaf42023dbd,0xf8d10419b4e02073fabd,0x5da8e2a0df87578c1ec6,0x1d9e003b1df51b6402ff,0x664c172a4c80f020060d),(0x1c4ad54a54274c9101d3,0xd09f3a58911162008014,0x80040c23760b15aa4e8,0x812e1ab25cb54a54414,0x93c74d192c4c58702005,0x76e9c3762bc507020040,0x8e5bb566c8781003068e,0x15c366ad180504001810),(0x68e3868a0304040040c,0x4010e245428300781003,0x8a102478c023400e7cf4,0xd2031f860010185781c0,0xc0a01002e806bb0e0098,0x2f570b55a2cd64b1582b,0x8d44a1ec662b0580bf5f,0x17070140601002712402),(0x369a4ca55289348a3d1c,0x124028dc394ca552275,0x32143007030140803008,0xb4b24d229047a2910874,0x6010008c380286a75389,0x84a24110843a1a088100,0x40a00fe1a8d066321489,0xa84c0a030080192ca01),(0xd96c34da4d166b3196c3,0x20027958051a8cc45b4,0x68b0572a9409c4d0200c,0xe00a2f0332990c662309,0xb0d0642c0401804001d0,0x300158a852281387c3c1,0x88a03008008804274660,0x94ca45027934984b2391),(0x8005e2e11c1e065a2c,0x30168b04822108800803,0x86e01460763a1c8cc64,0xd8ea71381bcda140400c,0x145e28823e1ecf4793b9,0xe098480a03008013ea80,0x8b75b2b95aac54a9d449,0x500070200400964380a1),(0x2612e8a44a210c854220,0x280c02005b2a0050b85,0xbe5bac560af54a9c2e15,0x1603008000845013017e,0x4ca451231107e3e1e834,0x200c02001f8f805072a1,0xa2492082401e8f01e0d0,0x803008006e2f01401fe4)),
((0x874391b0c4602e1683c0,0x80c02006db79a9162190,0x73b85c0dd6e35dacd502,0x50180400fa78809d2e8,0xf2f479bc9d6ea0b83014,0x5c0a0300801a4c3013ed,0xd441a6d16833d9cc4610,0x471854260500009d8e28),(0x4698d3c1deee76b99cae,0x8d06733170b60100010e,0x153e028ac18e873359a,0x5528942a04f060060100,0x800010f202572b558ab,0xe270379b8da693419812,0x400a0300b5004ca8b9c8,0x1385c0df6f361aac9090),(0x60883c1a040180084370,0xa03013e9e3168290c703,0xdf8fb7bbd9e4180a84c0,0x204fe7e0200c007d4022,0x4804086b01426108d46,0x28b1b0c05f2f174b85b,0x8cc55e2e40a03002e976,0xd410040081d04026431d),(0x2cac0289a0cf0773b1,0xa82188c2572a83408010,0xec75b8dc403013d1e6e,0x5f0f70280c04fc7b3d5e,0xa914605008014a994d3f,0x63809d0dc0800404e76d,0xb458ac0320e0200400b9,0x84c15faf978bb5d2e16e),(0xc0200240f405278ab19,0x38f8783b0d0582813088,0x14a23b168292c94492,0xa1c0d860260d018044e0,0x2462a148a04c200f8783,0x1c020029970052692c9,0x2d158aa522893898180b,0x17602fe526130178ba5b),(0x66b258abd52a70200401,0x622b0660af97ab65aad1,0x5a25108742840090a002,0xb4d2652e9449a4922904,0xc8509010020085809429,0xd2c9547a391a8a44a210,0x5002001c0b404994c25,0x190c4602f170b048220c),(0x10049daed690c186e33,0xa2d06733598cb6532408,0x400109300a29116ab49,0x6ab150a75327c2e12020,0x1004a4ea028c2d96aae5,0xc74399c4d6160a04c220,0xc010f2c1a2267c3d9e8e,0x97cb65929948a04f2680),(0x400400067600a526933,0xf77a3c9e2f077bb9dae5,0x3e9e4ea7008005680a4e,0xa4f0883ab958ab55281,0x291086422086002002b0,0x41880a25032a9508e462,0xe261288c421e0b00c002,0x40040898d64520180a04)),
((0xe470371a0b4582b0180,0x7bbd9ea06883e4043f1d,0x28a3fdfcfd7e3edf4f8,0xca6431988301107800dc,0x1d6e7744aa047037998,0xa4461cea74b99c0df6f0,0xc6db65a8009002805278,0xea301479c8e371385bad),(0x612a5522892290020022,0x960ae010005026028d46,0x70300529879a8d0672c,0x266d365acd569b280800,0x8ac46181002006945005,0xf9ea0600015fe0268b3d,0x285410f20145e2b01803,0x76300a3d1c8dbd1e6e77),(0x504642e972b80703000c,0x4f2783b834120005a040,0x860280d00058fc0287c3,0x801188201211007f3e,0x3d204e30c4720c2813,0x140004384050d3d9dce4,0x6c351f84404e471b60,0x69b01e003b1ac05298f9),(0x2c0900c01000837281b3,0xd0e8374d53288c1cc370,0x219862d855ed7557cfe3,0xc62f8561484a11815ce7,0x6e5a9625691a438d2328,0x9aa5a929d97e5e9765c9,0x682a010020040069c0ea,0xb02548a1f87a1b85f1),(0xc5ed7b1eb7a5be5411f3,0x821f87a1c865f67d1f27,0x22839ce6d972428ba268,0x40da3e8ea328ba2a89a,0xd8691805b16429008000,0xa5525192227c8d2107b1,0xf1fb7e1f57d1f07b5eb6,0xba428921f8721a866177),(0x4aa9aa2a7a3a8ba26749,0xc8640b804008016c8000,0xb1e85a15e370d42588b1,0x721b7f1fb7ddf37b9ed7,0x965c90a2d8ae2a8a6288,0x40007693a4a8fa3a879,0xbc9c244881e039014030,0x9d073dcc6217e5bd1c3),(0x1e438fa3b8e2378d20d8,0xd414986609725b9324b9,0x94670c00600801000046,0xcdf07a1795cd3f4d4ee2,0xa2e8b62a8a628886207,0x1ab04692a428c99e639,0xc465184490b406010020,0xf1f17c1bf58959284851),(0x926390a2e89a248861a7,0x2d045aba4a91a3e769,0x1471194610300a008010,0xd1f07b1ea711625648e2,0x4a91992268962488dfb7,0x801f01c010024b4c9d4a,0x260480d9e6354242cf62,0xea5d96e59926408ee3a8)),
((0xc01000b677c21a9aa29,0x759160d7f501062bc3d0,0xe3b8ce14775d16bda66,0x29181a9a827c9764b9,0x7c8d1d86916c59114010,0x8e1f7edf47c1b8631282,0x2db204a8ea2e8aa0a248,0xa0961904a0b804004002),(0x89f97d9f56a15e32cb72,0x940fa468e9ba6590a298,0x47d1b46817808004006,0x6df97ddf57d1ef49c922,0x5290a328ba1e6290a1c8,0xd8a01f03b0140007d8d7,0xce11801ff7651742d003,0xf2779865f9724f90e348),(0x20fd3cc9d14820001930,0xea5a8e236849d24c1144,0x1ce72501c00400225cd9,0x235725c7649804b9134,0x866096e5a92e4a91e439,0x503801403004002241c9,0xdcd6498a600fb368d22,0x765c912438521182a088),(0x28370d8010001b20dca9,0x420f83a0662d5f3f8e83,0xca609765c90e358d2328,0x588b0b81200400578646,0x72428b62a885722a09e2,0xf420a428da328aa22659,0x5083f49d00c01000058,0xf23b8e6117f9d7749936),(0x15e6c0139424c906408,0x993824c630b808010010,0xbe6297242885f77b5b25,0xc010000572c1ea4a749,0x36036857d3e4860e8090,0xe65c932419023f8f63c8,0xcc740c816004006ccaa6,0xa1a7e5f57d1825a4f82),(0x100126d6e6d697a5a959,0x3cc62f0ae294300500a0,0x8a95a528c90a1f875f03,0x594b4f90f0140046c3e0,0x3a3581dfd785db6d1965,0x40072d0d07a609424f9,0x3d023b4e128c8f1dc3a0,0x6e7990e3b85a0a80dfd6),(0x288c20c4e01401000370,0x56128460b7298b374d53,0xc01001db08a5c962438,0x49fe61d0f40cad024050,0xac11a865e932439023f8,0x58cb2e05c1242d004996,0x8a5c90a2d7a1bf5ad623,0xac5d008010102c042919),(0x71ed6b54a4f4a4268871,0x5190dd4a1a6398a298,0x357648d0b3d83b0e81f0,0x1d09e26183e0c72d8f6,0x216f3bc9c13c390241d0,0x6e5995e4b9263d8f2036,0xca925c2400199458409,0x7e12845d874d514c5213)),
((0x5001000226583e9f6799,0xfddb4f92c43d032ecad1,0x1950fc3e9f2798e2017,0x594b4a51943023088010,0x2c9f67c94a4b849db6,0x909a2408718810002902,0x3a739ba1b7c9ad528ba2,0xe85f0a8290040069c0ea),(0xa216a550518b22287e1,0x8003002430041fa1e869,0x5611751aa63542400ab2,0x2c006c02f04e4c92a318,0x95745c566538be29c631,0x39271d0a468ea26669,0x3643821885f9043e81d0,0x242055b39e25e976599),(0xf1f55b0cd2e4ac288310,0xe541a7a5a95a52247,0xb62a8a6247dcb017c2a0,0xf1f5a5a1e859d2738,0xa268915b2045e11c2b0,0x836069c0a4289a1e859,0xe9f97e0f737ccc134350,0x34009d2246a699a56427),(0xb6298a1462607f114290,0x780f0015b0ada59d6718,0x16628a61e534bd248811,0x7448004004adad0b28aa,0x8a2a8a628875e82406b1,0xc3e0f40100022645db9,0x1dca9de4590d964950f4,0xe3b718dd3547306d8b9),(0xcc0d9c0a8e5791a459,0xa9f06518e49101068010,0x693c0026110c279a6688,0x27e9f63079de46edac6,0x2ce8224370711590c00a,0xe5bda8e9e9820c729c96,0x2570445053c034000c71,0x4000060346f6919aa2d6),(0x5a94a4a8e909f45c1053,0x6d2d0e81e001023b4e1a,0x65e710e799de5d919a16,0x696d555444f134388273,0x90a60992667042952166,0x9e77952127f9dc755c15,0x696d1604410c030a0000,0x3305c029564b8d5c56),(0xa642885ef6dcfc36cc10,0x24820700062838736959,0x844165e5e976593c4d22,0x3a3b7956755d1e158259,0x1d3b004000a1e61124f9,0x99d510a348460867d535,0x4de265d6753136104264,0x15394bd1e78825106778),(0x89ab0b67c9ee4368d975,0xda758921f3588e044005,0x1c182d4346f5620b69c9,0xd5bca6297a4e18394d03,0xad906190e134190046c0,0xd0630bc0024c136c2939,0x3974188a4a2487db65,0x1a4791607440e4074010)),
((0xa1a91fc45034000a6735,0x14290100d6a5468aa298,0x952f106829c6708990a1,0xde6180de578997571570,0x7141324bf095e2478419,0x8400645df0f679795975,0xd02f9ee6196e518f5370,0xda266c166344630025c5),(0x8940448af001df0868a9,0x44000ec1f97e4e90e0f6,0x6e5c7518d42cf63a8a01,0x74831d4730dc007298b0,0xb04c0c5eb6cc1592a0d3,0x397425c895f46e8e02,0x2e3b8e2096204f074010,0xd8f4a8ed3841e0e8007),(0x90700080100036702489,0x1000008196f22d8b18e4,0xe0666ce9a90a26890350,0x357c3b0c52e4ac288155,0xdd245c3c0ec00080036,0x1830050006d4ee2ba459,0x60284ee77112925b8e33,0x99581124f8d5e667d471),(0xfe818056150cde0a0017,0xe3b78d484640008d950,0x11837c01068020da4c9,0x86f3709e0ba949b2427,0x3c470ae93989f86c95e3,0xde428a5f66b95b2f4000,0x6dad041bd594340cc186,0x29b7d5f46949a2402c5),(0x61183acdf35c369081a7,0xe8d30cc02000b1909b7a,0xc43205c020ce426ddf55,0xfe943d4162cc326e55d2,0x86517695408c00976090,0xde3655484650c08c3f9,0x80e9310aa059b90ca7a8,0xfce92a86a05832a5df05),(0xb8a5051b50c262909693,0x1e00fc23a2e629096e2,0x10e60527b78da04cc030,0x9c0e909f57d1b55d0630,0xde729c62d4e87e0a8006,0x46659922d898f20cc176,0x2e43759834dd120843d6,0x79c3424830dc1b001ca6),(0x1275909e86c8008b42e5,0xe53799434ecde5a8281,0x661669634f13409de71,0xb5e253d454bc25795971,0xb25c7e16226411125ab0,0xddef52887174106b4ba0,0x9b390a297d58405c336,0x3674696653e0d80c4150),(0x7c000ed8da1a738b55b5,0x8275104315e9f8dd170,0x94100c014e4259fd641,0x326289ce63202f04de27,0x9e7e820400003f09001a,0x3dd264e89a107a1182a6,0x79d764d814827b97c3c9,0xe51799775619f1125a7)),
((0x85d81019a4f027569e71,0x800064e500f21281d994,0xe24e72c05078500e9b14,0xf10e0d6772501c7358a0,0xdb46583e08a8f7ac6c6,0x15ad9dd9c4d842756619,0x80292100d5194a2d048a,0x8424101e45694909c431),(0xf1400002114c3d921d84,0x1b55b8309e243148200,0x742164665640356f25c0,0x1277100950a80e542474,0x5db70ce21339bc0d6488,0xf839076716969b0ad7a0,0x282c6b64d74c0900d885,0xb95e4683a63e490f9965),(0xc5a41543f91e4544db20,0x1b03999f110036cce00,0x9b90084200e760c1991,0xcb4aca8140400100c340,0x8c8c0bc0400101409d1c,0x19cccc8b800040815ada,0xd89857d74140400100da,0x9e2423e30fcf81004000),(0x4001009e9e5dce0d8dc0,0x488857c0c0190a4a0140,0xd98100401940c1589797,0x234040dcdbcac0401c80,0x7c740079580a3cf4f00,0x96e1e1814100400088,0xdf4d40401f80c9490040,0x15d600dc8b4b005c00),(0x4100d110c0118180d647,0xd655c6d60000ce414000,0x1c0a0c0e120e0804000,0x88c04001014090824002,0x8009c040a00040014100,0x9acccc8c400098c9,0xa222e1c0a2621e014041,0x9fe24000806222a16240),(0x15384c081014ece8000,0xc14d000100c151c00081,0x8001008145c0c0400100,0x8141004001008147d5,0x244040d282810140c680,0x4000d100514000e3c0,0x9c5b9a401b4084408141,0x808101504040901cc0dc),(0x80c0401d80c500810164,0xd2d200c0189840d84018,0xdec0c0010140d2d25200,0x8000d8084000dc800140,0x401d40408949010092c2,0xc01540e3a3c0d5000595,0xdf0100c39340d3d400,0x8640968900818000e340),(0x4dc10080054094c60094,0xe400dfc08c599960409d,0x9e408340c480d2c0d440,0x83c084008e0093009700,0xc6144040a1d3031b02c0,0x99e38a17db5d44d24481,0x2ca24718504099f306aa,0x690a481d7175954d03ce)),
((0x592285c2480c1029a8c2,0x5d33ce34a00132db2ba2,0x85101a673207dd6da658,0x9040400b8816a9617de2,0x68ad526488909f305850,0x5263c38301f3d78e1bb5,0x80e9c365c988080402e9,0x5a3364c582d529522344),(0x2234278d15031d40098e,0x437eedd315eb95294e95,0xc324470d18180901e023,0x243438384d804b9115b2,0x8764f74eca8530652298,0x96b94164f90a8156590c,0x6c412eca946903745305,0xb6356a082081bb1434e8),(0x9f4067bb8b3ce0d3860,0x827bacd100778d8ab962,0xf6ac26177a83893a5b0c,0xb170a8ce8825a7dd6256,0xa4daa0834be7af3c19da,0x60c07df2f052420ddb1b,0xce116db549306953f735,0x96c9c8313d40f9770820),(0x9e61606429b8419c7351,0x69b99156ccbe849369b,0xc51885572c02338bd8c2,0xcdab4582593e2b30643a,0x1e5973989abe6d458de4,0x3e9996b018449aabe752,0x8a6e59057936b315dcd5,0x625f440eefd38706933a),(0x9cb179c92c55a5172ca1,0xad1a6940e88a80b65d68,0xab1c83c14bc106208086,0x58d00e31849046318752,0x1548f00375c3814e17de,0x34e4cb6c64111580402,0x2993852001ce04781428,0x4210e6800920c110e257),(0x25af439a356bc70a890d,0x9924cab0a5b7598adda3,0xb8ad55944c14f21ab461,0x61d15800c95984eda073,0x77e96a885c87045b011f,0x5c36c440eac6674160bc,0x649b6c6a9c14940ecd7e,0xf115aaca044d9ae7824f),(0x9a36dd48110a83bd3801,0x2210ebe02d2e6a439564,0x207c4240cac7841ce9f1,0x6d25174752cd7473f03,0x5652b101eda67c46cb79,0xc60c6d70942c46a97239,0x26033384299c2175814c,0x940b3940944c853a683f),(0xe3944b2206fb602f8110,0xacddc148e8255e9a08c4,0xe80a70421128c50630,0x4805159e26acc9024af2,0x18ecb008040104784321,0x6659f9d9c19581756955,0x60f8f088541c0108c052,0x45800e92766a0dd1a585)))

def page6 : WordPage :=
(((0xf9c19504e8b4b0784000,0x80140400fd9c4a5a4e41,0x90468a61e1cdc96d58b8,0xc5995d00b8b47c480011,0x50f4900110c85a7e55e9,0x188852a27a11f5e5b9b1,0x91a585453908f0c00400,0x89210cc0bc4c188452a6),(0xc40401a08c569e6e19dd,0xb47c468205d5716514,0xd0609a8e7de9c599000c,0x10b8822615fd4d1c2800,0x30d869e1cdc8fc480400,0x105c26b222094128a004,0xb0400a7a71e5b98cf4cd,0x9600cdf9d97504780400),(0x753ce4ae85f1bdb5ad24,0x1c70e130aab65e4a35a8,0xd4c404008c541e3a2e2a,0x489696220928a068d9ed,0x400c85822ae31accc5d,0xd11e452cd42c9c651090,0x346d7c4c14bc86986098,0x743c7c00b40c463d34dc),(0xd49d7800c050193c00e4,0x50e0387000e43c76a92c,0x5c2400d0602800e0703a,0x74b0400800b848118ccc,0x1cd86830d42c6534dca5,0x45689abcde321078c454,0x7f5e0eb81c7778008071,0xb0116482e04dc0bc81bb),(0x34460880920166035100,0xa830ac0320d334080814,0x7c1a3030a69132b142a7,0x100ce684443a54b744c8,0x339b39460f62d4941ca4,0x578506a0f620e520c20,0x2b54a54274c9522344b4,0x2021405766c98b05eb96),(0xae3460b14244070c1018,0x70d9a3260b15280401d,0xa94a84e951014c02bd9b,0x684f9d34057996ac2c56,0xa007b5dad8ad56a53a54,0xaefdf3c76e9cb86ed9,0xdaef1db568cd9315eb5b,0x855d0a0386cc980200d1),(0x5d78b121c18004046,0x263cc015edda1a305091,0x29d202028d7a13e74d97,0x549910e001011ebd6ab5,0x96015c992203c700235e,0x1ae0c1000e16b972a508,0x9765a027c01ed73e7902,0x26178621085072863120),(0x2602b024102721802a73,0x3fa7306b4026e902af8a,0x22c0db74103b80ebb810,0x71c100a003526101a810,0x680cd381c76f81059010,0x1660248b302b005e74c0,0x8202182201c603890320,0x118d0c480a1ea0b832dd)),
((0x487e110311a426a83043,0x7e782355a94f1826040,0x20280b90b5298263c08,0x204021a623262b75a4c1,0x88d810152d07b3322315,0xd19c2c0403d8c1a6c554,0x3334670b0100ade869ca,0x848ed121d2e0404f5816),(0xf3c116a5304c7810079a,0xda0036ab5298260400,0x40404d0f6971f2840681,0x9c88c02007026f522aa4,0x70896e5488c02013825e,0x804b20258a50d828017,0x19064c7800879fb5263c,0x10040c834c7c80d0200a),(0x1c30080349c12e4c7c68,0x8daab346700069cf5791,0x30091046971f32400032,0x1217240402c68150151c,0x353c11a931e0403f901,0xa5304c01e1e112981e04,0x94c0ca101a040364c0d6,0x180400e3408f901a0401),(0x68d39a1c0402f2209391,0xc1400752c4b32c040065,0x2cc410a5081014ef08a4,0x329420405388218a9020,0x81008ce0666ace0002f4,0x524f8e920201a3e0b395,0x240402c0ad0901007560,0xc9c114200401f800da24),(0x15f1d00b02cf40686001,0x85aa4400d87646c0a20f,0x4b05001d521389c00935,0xbb62a62211176930c200,0xd0d500220ec8080786c3,0x73d6008ed029c2c055b,0xf2a63b42a69940201b40,0x8c54476a4421950808aa),(0x4439032a10aa22ae0101,0x4a111666297621881016,0x9b8ac83bc546e68798ed,0x6ab1804e0cf4080aa1a6,0x4a123807d3c2a30318b0,0x35c0dc159000bbed4f00,0x5133607140b20f629001,0xee898e14e9f2902b0bbe),(0x1602adc13c641ec4b132,0x380b8844a15805641742,0x88108180988208288308,0x8354660d0ba48a0a8505,0xd23105c0441e41852055,0xc2f48180698f1815405b,0x240330c069c10504b158,0x1807028044c000104689),(0x89207b228f870341504c,0xf56ab15173365a4cc63a,0x401001f150b5da6c762a,0x953a9545d4e458138761,0xc020054cf00569b0d5aa,0xaf168a54a1c0cc5c2410,0xaf5467d329841e00f778,0x4600802387c015aed364)),
((0xc2db6424916853a9b4d0,0x96c762af572ad55a8c95,0xe13402004faf0056bb4d,0xc994c2330054a65288d2,0x767b1d8abd5dac54aa33,0xc660e0480400360137ad,0xbe1d4e46c25492441e8e,0xb580ad76ab258ebd58a8),(0x72371a4be592a80400cf,0xb552a8c5219046eae4ee,0x800602b41ad363af576,0x194b6522611c52250f8,0xbb4d9ac963a9435f8f66,0x83d1d8d8020058009f16,0xaaede502692a8e449388,0x2b57e02b4d9ac95eae56),(0x9c47a20cb632cd50a400,0x63af572b556aad4aa33f,0x7c381a0b85402005aec9,0x72b153a83d1cca23d940,0xe00ad569b459ac962af5,0x7499d858271000c00c90,0x15eac55aa953a935186b,0xc8c01004b4fe02b5d92c),(0x481c2d361249167c3692,0x32809e16bb1d7ab9519a,0x5788c1980bb571308e0f,0x56eb6daecd63b0d6eb5,0x29067e2a13c02004dcdc,0x358abd57a9429e6ec47a,0xe4f260b64c211488f68b,0x957a9d4a2d11833c180a),(0x53e9446dad5e02b357ab,0xd4aa33a994c233005a2a,0x3892c0075015a6cd64b1,0x52a84d262e16422cfe7c,0x1012b80acd5eac55aa9,0x5a10f86f2c07a3b1b004,0x57a3f67b3586b75aabd,0xa0100400a6454a2d2020),(0x55e99be9e6d147a0cfc7,0x8040100495171cb5d9ec,0x55e5ee16db2124713691,0x9400ad40234d6ecf5dad,0xfa50a6d1e8a419e8007e,0xb002b5da6c963ae54666,0xe1c8b055138240100379,0x680ad769b1d82bb5ca8b),(0x58f4420ad7632a000d05,0x301b759ac960aecfe713,0x1bcb02e9107636008089,0x450056bb559ebd58aabe,0x67ae4e46e2f9643a0182,0xc08300ad76ab4d9e2f0c,0x370d7e1ccca602905c00,0xa4f0015aed367ae556),(0xc4460cc0571588e42008,0x501592b961b5daac75ea,0x75d89bf5f062220f4761,0x90602004e6ad5eb75aec,0xd8ab1529dbcd62a147a2,0x5814c920100560055cb5,0x2b3592bd5589bf5f0ea,0xe45f2c8c44801001a63a)),
((0x20c02b4d9eb91467ab0,0x6bf180ae3011c4a19008,0x1004f2cc02b556aab528,0x9327baf13e9933184b80,0xd067e3d0011566015baa,0xac957a94a204fa70b7,0xb358eaccf348d4480100,0xaf54a50b8004cd78056b),(0x3a02b5daac90e803dd82,0xdc692f964743500452,0xa806c9140157a4ecf622,0x49245e1904679c8be591,0xe591a80401278a00acd5,0x55a8eb599ebe401f4b,0x572a7519ca6d06582780,0x13a2a000b5da6c963b0),(0x64b1582b558a99004e0d,0x680a0100054c7735a6cd,0x95b6bb3d79b2d2660f0,0x950a71188835d8cbf680,0x74b004014c015a6cf61a,0x54d9648a06f573b81b4a,0x5c4ce5ea3002008d3540,0x804015367daebf4790ba),(0xb5da6c7519749164720e,0x3795ca1368a2f3cc04ab,0x9434085780566b157a73,0xadf6eb659ab2fb73210,0x43cd4ca1451f800839b8,0xc673297ab80158ea72b9,0x602b5d66a343a0c8dc4d,0x2ad548b300c05b29578e),(0x1285405171140569b256,0xb2586cd64b0575cccc51,0xd57278de52260040002,0x44ff6d3340545ac51a37,0x1948ba014e2d761a54a6,0x880ad769af562ab51683,0x4afd76b0e13f9f0e29c9,0x2b0470f416f86f00ad36),(0x4db673acb6dd69b34220,0x13de76a9a481c2973f9c,0xb65ae733758a2804002c,0x63a8c5e290c001c8aa69,0xbca0220ec02021b5aed3,0xd4a353b000ad754843e1,0xfcf00564b1d8aa2ef6d9,0x2b257e7d0060abcd8004),(0x94b9142e06a748b81b40,0xe2b105faa002ba015369,0x1002000b00ac55ea24f,0xb2800056bb4b15026a0c,0xb0d6aad3470a8d2e75,0xc956a83004a1b00d7aa4,0x95568f451600160aed9a,0x83b4702eac00ab9599cb),(0xe3d00ac333945a6c956a,0xe283eb3e3b3955a851e7,0xa9370156eaf278a220b,0x4b40563ad55e50a64180,0x155669203892c020049,0x69b2d92b9132b911f0b0,0xc963b0b2440000324c05,0x71b66d340bcea00015ae)),
((0x3300c04c013c22366a94,0x4861a434020033ec3558,0xc15797152995e586b52,0x668e14959d467cb4cea0,0x1b4040034470eb69b1d8,0x388ac01669680a4a923e,0xbd5c21c00ca0138cf875,0x4620003252602b350634),(0x5da07900d0a88d45b8e4,0x8bf9f2eba75926d61ad5,0xbab200c85fb0b3e2f52a,0x55a793ad6c00a743c056,0x801665318cb037478000,0xd8ab16bb257ab1541800,0x2d8940452af548ce00b4,0x56a896ab155015bce66f),(0x562ac4a800f9a700abd,0x84e202b053216e0a6c88,0xf1749c3b0159a6846003,0xe408c83d521080ad3546,0xace5ba4d0c3064820055,0x800669800ab1488d51da,0x80ad6a21f0f198029bcc,0x8d3397a02ae469d2e25e),(0x2abb6d2e8b3680a8f40,0xac2a0000ad35eac54482,0x9ec95ead55aa401b3d72,0x291e22f0832b00400b3c,0x8298d9bd49014269ef23,0xf2e0157e6512b180abaf,0xc055da1d059402b056e2,0xc6d801b000098001b39a),(0x275ba98f56d5480564a2,0x48012f8ef5d013a9bc82,0xd6f4012b5513d0155d7b,0x8ec06901592a6c0010f2,0x1582ba2b01545443e015,0x26fd8eb83f0052ddc010,0x861b3d5519550129a670,0xc27640d85d022d0c4c92),(0x80abb5c014eebc02b4d9,0x13e93602a2b68053c83,0x23a044051d4400a3897,0x3b4e5b59160000120408,0x4c0516011e03d693e499,0x261844b5013500501014,0xe8a64d1c80400767b009,0x3edbcc64ca51208a401),(0x78a44e250d854220f048,0x4180980400e12080a331,0xd127f3c96494461e0d46,0xc522712874320b048023,0x218bc02007946805198b,0xd1642c9248c391b8d263,0x5138742209017c3c5ac,0x75147a2690802001cbd8),(0x7c220b0480bedb6c660a,0x1000a5b0028d45e27128,0x471b8cc5c2611034120,0xe250e84411b8c2459ecd,0x48180200801ce4028c5,0x802c1469735998c24c22,0x2f0080232028d4662508,0xf26d3450c81391a4c6)),
((0x218fe0145e271285c12,0x2365aad066b1d7691368,0x7680a33178943e17078,0xa62a938622c12078026,0x805178ac52190a84c117,0x15068300b02802000cb3,0x9147e311587325786f2f,0x29130340e0200801b03e),(0x43188b431b895459a08e,0xccb6551200400787680a,0xcc5e250f85c01ea833f1,0x8128440c01002e57e028,0x5198b4561d0a571a89e4,0xcf2591a84c02008c0e00,0xa411e8b431c293449f,0x2c14498442006c02e700),(0xfd01466290480a8d2e61,0xeeef7633d7ab759ab400,0x1a3e0146a2f1287411,0x6401b07b1b8a44c10008,0x42b805d0fc0145e27128,0x31287401d4e6542892c7,0x4320b0500401123780a3,0xe404d2671dcb4271187),(0x84411ec99400d802003b,0xa0000468028d45e270e,0x311689c4218ce3e88032,0x2e14d8148005c0d01486,0x800a31168ac4e210e864,0x44009f31e8711401158,0x10882401d6e471a91380,0xa0200800561d6745e2),(0x38405188b43a18642f15,0x8bc393e893f92882008d,0x14020040006014763918,0xd1185fae568a72e15890,0x11ccb55126d3096013f1,0x500400540133a2911864,0xc014662f128017868200,0xf15803015eab5414224f),(0x5386700401f2028d4662,0xbc805198a44a150675aa,0x88429187c390fc5e0034,0x70329809c7e7680a2d12,0x6ed80146a1b007132d4c,0x3a19003d8b84c2206800,0x3180b60100090f0028a4,0x8c9c4051287411dabe5),(0xf1684401ecdb63241140,0x4de2b1007400ce0500a2,0x80470000145e250e841f,0x8bc3a0b0470a4d123216,0xe46944923b0a80004e7,0x2e0e0001804bf8cc5a25,0x8426358943a190024068,0xb4561d0a4fa3cfe7900b),(0x380abd509b2840a00028,0x4130400200028a442110,0x1fa0289c4a11046eaa8a,0xc4e1f0b8441e00d75e80,0x4e221085d0080004f98b,0x13008006521014662504,0xe9187e00a45138638494,0xe4051a8b44218ee60288)),
((0xcc49a89e4c2210800843,0x3863cddae5001cd96028,0xe2206805b00001482311,0x1a010000a0900429ec6,0x9d46b1883b612a8b429a,0x145e1c8929118820270,0x1477af566ad0080218fd,0x2f08821f8ca00873b405),(0x3211048000014ce01466,0x741dfc6d8d30c0514874,0x10a0021cbf0147631178,0x401872c805183513c502,0x96a1014710c723718c5,0xbc05128742e00ed3000,0x143a110479248e4003e,0xbf2e000020601475da73),(0x6e5f528000512874218a,0xdc050e0046625007eb11,0xe802211a8a44a110169a,0x7e2a231138741cbe027,0x3120145e1d0660288045,0x1f8028843a08e95d0000,0x39c051a8c45a26ea2bb0,0x4d80a3eb04b9acc2008d),(0x820147235178240df8e8,0x28d4621cc400801fa,0x801198bafcac1a08818,0x13622b0e85bc9acb6178,0x2402422a68310e83e220,0x101112350e60a81280,0x5123819106310e8639cb,0x3d900de8b00a29048038),(0x85421cf048000a311488,0x148942208008000a290c,0x210c8531000fd7f80a2f,0xa2b0d401d87a007b00a,0x700a1c9a4a8f85d186c0,0x6300a350e8419002006,0x1b5180a31167b36d320,0x402454f00a26e75825c0),(0xbd8724d0000a35158944,0x85b2800f4013f62f0781,0x28bc4a00628c809b115,0xb2fe0145a20e12904e2a,0x911ca94e00a311585aed,0x8c3dc2892ca3c0517873,0x50147e30f240c38dc028,0x2890023505769e1425),(0x9f2a44400801108440e0,0x1163e9d483d9b67a8c45,0x87420d01f8eaa51c0252,0x28d39d2f0e0106e3512,0x8efa7f009c25207c8e22,0xa250b80320c6028d439,0xc3800028ac3a16fc280,0x78a43215080000a31087),(0xe8d4399a2f000a93076e,0xa20028c3606e02134612,0xa26b54dbf005180bc5,0x46998050f70c2996ed5c,0x1b0145558000e009ce61,0x50f320d014028e45e1c,0x45b00d00009a28689800,0x7009e4b2884021002004)),
((0x26fc3a2e0206806186c3,0x20286001fc02879d6220,0xd60028c439620209801c,0xae404002d95496028b44,0x8880a1d16013c1c0bb88,0x10020e028d4380524,0x4802871f404cc4e80a2f,0xc05080300a3a2001400),(0xc4587e8631c7ccb0a588,0x901410051301454490e1,0x40044c4a24868d924047,0x20dd1c17d71591d085c0,0xd71591d08440400c5c0a,0x904400401a0c09e0dd17,0x401949cc1fdb195896d1,0xdec95b1a189190458400),(0xd4d10fcb878381c0401d,0x55550f0d488040011c46,0x13900e43c00207c99d96,0xc54380400b9ec95f9e94,0xc180401e49075ddb910f,0x8040210a4c99d8d48f8d,0xbc003dcc99f1210c604,0x40014708df9bd41150),(0x400840c69c98578f43,0x80401e048a5a5612cecd,0x85c44011cc4a201f10cc,0x11d0844005cc4a20d710,0x5896cc0400105a09dd17,0x5cdbd003c2001f87c999,0x865b934781c040039dc9,0x610c98174e8a80400800),(0xc44a1d0c5f120604800a,0x85c440171c0a20d591c5,0xdd159084400c5c0a1590,0x4f48d8904400400c1a09,0x414708d84d8b470301,0xc682801b40c8584f4d83,0xa05e8e4bc2115cc7ceca,0x49db0c201e1210e10a4c),(0x995180059b0c11858400,0x9ecb918580401b194c20,0x9dcfc38b9ec945438007,0x44a00a5eda8781c5510b,0x548f834187491e15d0c0,0x42885c8d8140030708df,0x13c04e824819968ec01b,0x7dad242000e5e87d918),(0xc05a9dc79e9ad38e5242,0x1e548dc0004187534941,0xa10c8a544d8140401c87,0xa10c600448c8a6010c4,0x11cc44558a170440401c,0x207c99c108440158a1c,0xc88e0781c05dc95f9000,0x12804e8248154f0106c2),(0x1da879380400e5e87d8,0x8a4c9d5206210c934e00,0x858c11c5c05d0c520604,0xa00a50c01e200a5b1951,0x848a46000050ca5e0004,0x83491a04105fc9d5d0cc,0x1c46c2c0545c871f404f,0xc84680c0401a46964d41)))

def page7 : WordPage :=
(((0x408652881800865b4280,0x5d1cc6106120c930cc0,0x4a045c158a045d0a0c5d,0x47434914818749171084,0x8d84f4b48cf8340491e,0x8e4987d546c108984307,0xc9c42c886d6411c46de,0x911ecba0c5cc5d0c4a46),(0x48050b08841a09dec94b,0x2465a40c69e54874042,0xc308c3c9914bdf490348,0x10414181c2c064428ac4,0x54820604c246840840c4,0xae17b5f7ad3af15c1200,0xb0f19dd6b2dfb4ee3de9,0xcd1bc2fb5c862546ff0f),(0xeeae51d45b4ef9df0ae0,0x6d6bd410fe9fb1f6cf3b,0x3e79d9dcb9be7b01a3e9,0xdf3d7bc99b9ba13fbaf5,0x79fe3fbbf5cef3e83e46,0x4b86ab79e993588f5ea3,0xfd5f86ef3e3cda9cf0c2,0x29dacd4dcdcc10b159ec),(0x4fd4faef5df2eee7e98e,0x8f78778027565282feff,0x48c9fbf2b4dabca2699a,0xab49a45fbdf68eb0dfbd,0xe36e11defdc4d99d25c3,0xc0fa2f5bf10ed5ea2e69,0xe8cb84b7805252fafe2f,0xc40bd6b58ac3a5c9fc96),(0x77f11e99e1edaed30caa,0xd29ccebe6ade96cfdaf,0xe9ce79e58e24df9dd4d7,0xdafa6f7ff69f2af01ec7,0x482a7be72952b2ddffaf,0xb62ae1a8da0998f9408c,0x3fde3d53d06cb7c42be8,0x2c03ac9fe9f96f02e96e),(0xe8ae6de4ce21dd9d70cd,0x3bf22f10efbed2eb5ea5,0x2fe4fc3facf9cf7df52f,0xb319ff96483d6643a8ff,0x2ece4cc7c9cc41bc8b71,0x7e78e44e0fde4dbcd73d,0xff2fdcfb4f7df56efeea,0xdad68cc4c0fb38a388d5),(0x5ef8eebedcec1e90e14d,0xf98f8cf89f77f70f44f1,0xa9ff7ff0fdffc4fb8fa2,0x589e84e7a273569148e2,0xb2eadfa60a1c9d09598f,0x3ace2c93c40be9baeb80,0xef2eebee62dffda8d7ed,0xcdcc6dbadaf7919fe1f9),(0xeedd9db8d90d81d66d29,0x3f0eeededaeace48e24d,0xfb1fa0f85f7df66f3af2,0x3b526351ffeff8fdffc4,0xb9b395d90d8b78457af7,0xb75b31b09adda77a2f9f,0x20ce6c6fbf1bceba1b8d,0xaec7e6de07dd4da2d4bd)),
((0xd05c73bb9a4fff4fe1f3,0x13dfcdd2da8d8ed82d72,0xceace99e6fe61e4ae3ae,0xf1ef12f06ef3ee3edaeb,0xedfcffacf8cf75f65f45,0x6ff6635d03c422effbf,0x9ac95691d8a68608397f,0x7db4eb19af9a8aa6aa10),(0xfd05ca1c7bc5bc35bc6b,0xf4aed3e7de31dd7d8ad4,0x7dc0eb4c960ffdfc6f97,0xfd86d43d37d24cefcbec,0xe68e58e1cdf2dd2db2d9,0xd6ebfebdeade7fe6fe6a,0xefa2f92f64f3af09eebe,0x3391ffffeff5fd9fd0fb),(0x3c7e277f70b6625bc542,0x3a029bf9589368c288c8,0xb20b06aeaab1a7fa3fa2,0x3bc5abe8ba2b86b64b3f,0x3f2ceebeb5e74e4bde3d,0xc7ababae59c0fa5f8df6,0xfcdd1d92d67d2fcf7cc2,0xe65e55e45e38e2ee1dd),(0xedeec4ec1eb4ea4e9ae9,0x78f6bf3df0feffeeeee1,0x9feffe5fd8fbefa7f7ff,0x7fb75f68f6324352e8ff,0x56a109df97291f8d2871,0x2c14bd2b5cb3caf6ab2a,0xcf3cd8cbccabc84c4ec3,0x5bdfbdb1d85d4dd2fd17),(0xbfcafbff5beffed3e7ee,0xcf6c97c3cbbbaea96eff,0xecdd7dc2d9bd74d50d28,0xfeb7e87e4ae32e0edffd,0xf3bf2bf23f20f0eedcec,0x93f7cf6df60f53f48f43,0xefeefebfd4fbdfb3fa3f,0x60b5dd5984d03211bfff),(0xd8c87e17a3720650639,0x9ab4a58a1399095a91c9,0xbabb94b75b56b47b20af,0x82d3dcc9c2fc10bf9bd2,0x4eddebee88ddfdc0da1d,0xb21ab6f9cf8df7ef67ef,0x1ac1ac1ac1ac1abd3b8c,0xbd37cf0cf0cf0cf0cccc),(0xdc5dc5dc5dc5da2d5bd5,0x78e78e78e31e0de0dde9,0xfebfebfebfe9be9be78e,0xf95f4ef2af2af2af06eb,0x437b569b4c2256fddfb9,0xba45a149f69b49378fe8,0xb72b59b36b0baeaaafa6,0x59c40c32c0cbc0ba0b7d),(0xad19cedce2ccac9fc63c,0xe40dffde1dd1d8ad66d3,0xa3f82f47f2fedbed0e5c,0x5bceb00a608a2fcffbff,0xdc0d90d67d40cc6ca9c6,0x40e2fe20e14e08de6dd8,0xeecfec3ea1e69e60e4ce,0xf3bf28f23f1cf13ee7ed)),
((0x91f8af85f80f6af56f4e,0x7fcbfbcfb4fa5f9df93f,0x5874fc370209ff6feffd,0x2080d7b776f70d6c25fc,0x39a095d9078e08c78608,0xa7fa50a379fc9dd9c49b,0x5ebb4b26b10af4ab4aa3,0x4de7dc6d80d61d13cc2c),(0xf6cf3ff2be8ce73e62e5,0x3b9c9ff5fd6fc0fb2f99,0xad3ccffcbabb0b18aada,0xe08deaddbdccdbdda6d5,0x72e63e5be3de35e26e17,0xeecee99e91e91e89e7ae,0xefeef6eeeee6edeed6ec,0x42f24f1cf1cf1cf0defe),(0x9fe9fe1fd2fb4f6ff51f,0x7576a25cc51b33f1e5fe,0xc58ae89b8518227e47ae,0xea099f299d95f9388f28,0xaf2adba89a6aa49a38a2,0xdbe0b92b52b3fb24b11,0x9d28ce0ca2c83c4bc28c,0xeeaed3ebae9fe08d7ad4),(0xfcff6fecfb8f9df8df60,0x6bccb53a9c9d49368b1f,0xd0fcf2cd1cb4c93c55c0,0xcbda6d95d84d63d39d1c,0xee16e0ee0ee01df4de8d,0xe69e5ce32e26e26e22e1,0x20f14effea3e9be97e7e,0x5fa4fa0f98f73f4ef20f),(0x3f5245ff8febfdefd6fb,0x8c66a6526225d2563504,0x17cd7367116e46d16a16,0xbb2b03a71a1498a92b89,0xa6c99c77c6fc67c4cc0c,0xed46d2bd16cf6cebcd0c,0xdecdb4da9d91d79d69d5,0xb7fb2f78f1ee9ce64e49),(0xdff8ff0febfe6fc4fbcf,0xbadb9eb69afb9d27e2ff,0x10bf8befbe9bd7bcbbbf,0xfd65d06cd7cb6c6cc28c,0xeceeceea5e52e37dd5da,0x7f01f01ef5ee0ee0ed4,0x4f55f4ff43f3af2ef22f,0xfaff9af8ef8bf79f76f6),(0xeefe8fd9fd6fd0fcdfbe,0xa3ad3ad000ff7ff1ff1f,0x69968467766664d64556,0xb7b775a74971b6ed6b6,0xc9189108fb8e68d989a8,0x95b95794a94a94293191,0x9997c97496c96c96c968,0xfaeeaa6a309a99a19a19),(0xc3dc3dc39c1cbccbc8ba,0xafda6d3dcaec91c5ac45,0xef8ef8ef8af8af8af8ae,0xfa7fa3f9ff9ff8ef8ef8,0x4d7d17d1feffcdfc0faf,0x1a9ea98a85a75a2a9b19,0xb18b08affaf2ad9abaaa,0xd7bd4bd4bc7b9eb82b47)),
((0x8c05bf5bf2be9be0bdab,0xc26c26c1dc14c11c0ec0,0x90c6bc52c3cc2fc2cc2c,0x8d55d52d39d26d19cd1c,0xe60e0fdb2d93d67d61d5,0x9af94f8ef81f7bf78ef2,0x8fb2fb2faffacfacfa3f,0x56327fff0fd7fc4fbbfb),(0x5d64164163563161d61d,0x66ba6ae6a669268a68a6,0x7577437337277237136d,0x4599b8b888f86285a83a,0xbc1ab68b48b3cac7a9ea,0xe34e20e1cd0dcf5ca4c5,0x5ce4ce48e40e3ce38e34,0xff0eee1ed1ebde99e89e),(0xfa4f98f90f88f88f84f3,0xd8fccfc8fb4fb0facfa8,0xcff4fecfecfe8fe0fdcf,0xbcebcebceb67a72817ff,0x6bf8bf5be7bd2bcebce,0xbc37c33c2cc10c09c09c,0xc6ac66c66c4dc3bc3bc3,0x7fd58d11d03ceecaec7c),(0x1e97e82e30e17de9da2d,0xf33f33f33f33f2ff2fee,0x8ff7df68f56f3af36f33,0xbfcbfc8fc8faff9df92f,0xfd2fd2fcffcbfcbfcbfc,0xeefebfe8fe5fe5fe1fdd,0x178240fffcffcffcff5f,0x86c84f84a84583b83183),(0xc88c38b589388e889871,0xa9b599398097b9688f88,0xa6da46a41a2ea0ca0c9b,0x40e0bd27ccbb81b42b08,0x7e97e92e84e84e62e4ae,0xef3eeeee9ed6eccec7e9,0x20f20f1bf16f11f0cefd,0xbf56f51f42f2af25f25f),(0xfe2fcff9af73f6ef5bf5,0xf1ff1ff1ff1fecfe7fe7,0x4c02b0879cffbff6ff1f,0xc59c51c49c45c34c34c3,0x7ac76c72c72c6ec66c66,0x5ca8ca8ca8ca8ca0c8fc,0xd3ed0ccebce7cd2cd2cb,0x99e84e3dde1db7d78d5f),(0xbf0ef0af0af06f06ed8e,0xf2cf2cf2cf1ff1ff1ff1,0x4df4df49f49f41f2cf2c,0xbf7bf66f59f55f51f51f,0xfe8fe8fe0faef99f88f7,0xffcff4ff4ff0fecfec,0x7146e86db67e67e4350,0x8918847e27dc7c379174),(0xf39f39bb9649459268b6,0xba0ba059ff9ff9ff9ff9,0xa3da31a2ba2ba2ba18a0,0x55a55a55a55a4fa49a43,0x3b56b49b43b36a94a81a,0xcb9c7bb7cb6fb69b63b6,0x41d34d2ecf0ceacc5cb9,0x9fa3f9df20f1ae02d47d)),
((0xfa9fa9fa9fa9fa9fa9fa,0xd5fc2fa9fa9fa9fa9fa9,0xaa5fa489976df6dffe1f,0xb43b31b16adfabfab1a9,0x1dc06bddbb0b8cb7eb63,0x1c4fc4bc4bc3dc3dc2bc,0xc87c82c79c6bc6bc66c6,0xa2c9ec9ec99c90c8cc8c),(0x4cf0cd5cb5cb0cacca7c,0xd02d02d02d02cf9cf9cf,0xc6d8fd8ad81d81d78d3d,0x9eeaed3e06dddddddddd,0xf82f7ef7af76f6df6df6,0x98f8af8af8af8af8af86,0x8f2dcbbfe5fcafaffa1f,0xc98c1efe3f79e7cd6ec5),(0x4fb8afccf75eb5e4cd01,0x9f63e28e28e01d3ccedc,0xed1ed1ed1ed1ed1fd9fd,0x66e66e66e66e66ed1ed1,0x7db7db7db7db7db7e66e,0xa20a2017006005000db,0xbf49b18d18d0f80dc0a2,0xf75f73c72170d6dd5e05),(0x84e84e7d277277076475,0x8ba1aa0d99495394988e,0x2ba2b1bb1bb19a8ba8ba,0xc9bc7dc7cbafbafba2ba,0x73d73d73d73d73c9cc9c,0x7df5df4df3debdd0da1d,0xe2fe2ee2de28df7df7df,0x37e37e34e33e31e2fe2f),(0x7e37e37e37e37e37e37e,0xe50e49e49e49e39e38e3,0x6ae6ae6ae6ae6ae58e53,0xce6ce6ae6ae6ae6ae6ae,0xe7ce7ce7ce7ce7ce6ce6,0x8be8be8be8be8ae8ae7e,0x5e9be8de8be8be8be8be,0xedbec7ec7ec7ec7ec7eb),(0xfeffcffafecf82f27edd,0x907607407406f062ffff,0x8908908908208207a07,0x5f3b426009409409308d,0x9a3e8887e871f60850b4,0xf35eb1e6fe3dd98c3,0x150ee0d20c007e04e030,0x32131e01b318b1711431),(0x7206685aa4222ef27123,0x58cd1c14b119f897c83d,0x55ea413000fbeed2df2d,0x85180c7f57e17d57af6c,0x9a9129008f08b287685c,0xdc71c29b64ac0a61a099,0xfdaf4fedde5fdc6d31ce,0xc799c91187c5b2000ff2),(0x2b53b28abba82a47a2d9,0xd66ce6c69c12c09ba3b8,0x5df0dee5eb8e8be3bdcc,264632415,0,0x18004000000000000000,0xca4e7675824111990280,217)),
((0,0xe03802401c0000000000,0xc8a91058a4292db14,0,0xf30f30f30f30f30f30f0,0xb98b98b8cb847b730f30,0xad000f25d21b98b98b98,15),(0x1501501501501501500,0xb4055035020015015015,0x6000decba37a65323931,0x65a49940e2b82021410d,0xb4cd3b3da7d9478717b0,0xa88f8397aa69a5c33b1e,0xabea93a4b9e798393b8b,0xd0ca5c4fc16bb2b5cb14),(0x6e7de19e0bdeed5fd26c,0x7b0000fb8f70f28ee1eb,0x9e014fcbf96f61e57b6e,0xa0da0da0da0c60c60b20,0x1291291291291291290d,0xc66015153ee329164129,0x9c3cb63a7796388a7286,0xe9094015000f14e4fcd),(0xbc2bc2bc2bc2bc2521bd,0xf4652fc2fc2fc2fc2bc2,0xb07a9d91f7b66625e350,0x96f17deedc4d1ac46b9c,0x12c123e16d082034000f,0xa9b9e48ab77263935e2c,0x26cf2ca4c70c3cbeeae9,0xcf7ef7ef16efcec8da9d),(0x6eb307000fccfccfccfc,0x20dd6cf8c1bc1bacf,0x805000004020000,0x2c0800001c0800001205,0x520b00003c0b0000,0xa0110000840e0000680e,0xe4140000c2110000,0x62170001341700010c14),(0x1c41a0001901a0001,0x6c200002321d0001f81d,0x2ec230002ac200002,0xc4260003782600033223,0x46028000410280003,0x602f0005082c0004b02c,0x61c310005be2f0005,0x4a330006e03500067e31),(0x820380007b0380007,0xb84c0009244a0008904a,0xaea4f000a504d0009,0xc453000c2052000b884c,0xd6e05000d6a02000c,0x9a07000d860a000d7807,0xdb406000da806000d,0xdc000000dc000),(0xdc080000dc0000000,0xa1f000ecc1f000ec006,0xf861c000f481f000f,0x221a000ff019000fbe19,0x105a19001056020010,1084431,0x10e8070010aa1f0000,0x721e0011341f0010f61f)),
((0x27cd1ce50011ae080011,0x637029574f2bd1ba7a71,0xf8db0646ad10803e3c68,0x7592c15e797873a2434f,0x29db994a11ae6f909369,0x13977cd67de94f00b07d,0x703b2b6ac6f7092c2a47,0x562ca3a892e87ed1bc53),(0x91d41e058596850ae26a,0x86081a40fbcba54b3341,0x592a8334dc31a6d6cba,0x68f2fadd2b05c149eacb,0x8e30ee9716ede8ebb576,0xe462460b7769d199d6a7,0x5ee55d9e8fc1e52be39,0x7a4fb0ce9bdd24a8f141),(0x3923674874d3705b619,0x66ae1cb0ab7187d70115,0x9d31ab5bcf6fdef11c7d,0x38eabbe7f81dc7e200ce,0x3e489b55d3a8a8140c8a,0xe2dcacc5bf416d57775f,0xda73b82adde0853a3f17,0xb3315c52ef000d0e05f8),(0xa5dd6bd3a581b6118f44,0x5b4c8db6b90f96f3bdde,0x8b5068775a8f23f5af8,0x1bd2eef1429b3adb5dfb,0xe921269d9b735c11d369,0xa3109a4e1444d0c86269,0x7afa5cc0211d68987bd8,0xb8be2e18740d350de521),(0x82cf1fc83ca8a7dfe93f,0xb6b6c3a089a074ae01cf,0x56aeeffbff1173d5da2c,0xd0e61fe8abbc0fe8cdff,0x3a3d251250be70c9449a,0x874dd7b2570bd73348b2,0xae8488eff19734f0b7d,0xfd4ac10e7ebcefad4284),(0xae9d4aff0024be5a2f6,0x642ab485e495e4c4025d,0x97cc2d24baafdae10598,0xb8e25759facb09726acb,0x60a1fadbd1d18713bf8b,0xf2427c8f9c81e041e803,0xa42f48706d5d5e1bb170,0xf4f6a052fbbb0b1484b1),(0xa2b68aa4d4ece3be0c92,0xa6026e3c01ce465d6913,0x9eb90cc7867dfe0df1e5,0x1d2c743061b61f6e352f,0x47999c487017b8a7f1d9,0xd13f48f9b38fb2567401,0x412a7cfc09a8a3b026d6,0x7bfa39792a1948a4e2ad),(0x77d256b0a558c2de9252,0x98290340cf5e968bc68d,0x6f1b1e4b9d1eaca744ee,0xfabb97b1ff35c6fe5d16,0x31142135781bb7a1f6,0x70536b8b0f90d425f26f,0x87293c2a010519282f4,0xf011362e925315e894d6)),
((0x6a1be439604c39fb148,0x193641b955fc5334d826,0x4c2dc7a2e2889fb7e49d,0x624e458f67f745f54225,0xb60109872ee933fa63a9,0x936e61dc28857a682331,0x16a5276566a7815629f7,0x94b485fb48b02bd2079c),(0xa6b56b421cdb261bda91,0x6d942df797ca371cd5bc,0x2a9d439796ae0d23892c,0x7bb1783f54aadb189d84,0x3a2ac00aafd3fd3c4886,0x84fac6b058a6caf06b96,0xcc220c26bf7d572e2305,0xe6a05a2cc7f0516fb20b),(0x6490a1e7c845c095d0c4,0xf9bc8764c2fb1923ff2d,0x2b2d9ae44eb74fb140f6,0x5ac41aea5aef75fe3407,0x78bbfaf1beb8cc89daf5,0x98eef2f89ba166ed5e9e,0x24dee865deee1e8cf0da,0x1a0e197afefc0696f51a),(0x7ca5b32b65842d1b04ef,0x97120ad60c1296218560,0x702096d315fee6374e14,0xe6b69ab51d9a00d3790f,0x4c4bf90bf2338cdf73e7,0xb61ea76fe5db18853943,0x90aa460a07dfd32cd18d,0xfbe634db3f173681cbef),(0xababfbdfc8e5a70da54e,0x56b3bb20de732409981d,0xc685425b13f63bb3a8ed,0x5a99a1f8e360bface1f7,0x4c7d038e3359a292e185,0xd32e4902114f12d3382b,0x1a235efc8a6f396a02ee,0x2d9b55708707299b12ca),(0x6c63c800de25e1bba2a7,0x6232474b75912986b013,0x886676393d6b9e0c7e4c,0xcb0c4b088a7a452bd8b,0x571a9d263be9908567da,0x2575a12a7a8ca3162146,0x15cfa913c5d732ecb0c1,0x616ce5c1e22b7478be17),(0xc9e14f17af1b2ff0d9da,0xf26ac6f1f7b186fab223,0x4fab7d8e0cad62cc540f,0x5b735ad727351305894d,0x1593c526e56edefa9c96,0x559eea5d5369ff8970d4,0x527b79d5860feca656af,0x54f9a27e16df9e3001e5),(0x4e003aaa21d4e1fe15de,0xda08bf107f129c445d84,0x8b1daf474dae1c5468ee,0x718ecf7f0f9805fafe3,0x2eb479b56e4d1b44d45c,0x5731a82cfef8db3efa83,0x97a605447cd1e9cdf7bd,0xd23226d95169ae14f52d)))

def page8 : WordPage :=
(((0xb4ebc27db47ad421cf3d,0xffb458f4d67017138614,0x4c90a4d19e754dfe140,0xaf73e217c303acf0757e,0xec16a7e246d1a542b6f3,0x88238ddef0f861b57d4c,0xda643e91426c3db58dbc,0x71088c35fe14485654b7),(0x9c5f9379c32003c394fa,0x3e31e61220aa703ed106,0x851929b152f709149ee0,0xfb3383fca8e622e8f438,0x46e6022e466249e128d0,0x52c1549abcfa6fbd41c,0x6f8c9f2fe80d10ee5ab8,0x205ddd6a8977feb0e027),(0x7f0c0e5f353b86f7d803,0x75cdfbd1745e773b0253,0xaef4c885cf2dec51da9d,0xd10e1dc65f42a95b8037,0x81d905f31c22b851696,0x31a90b2615914ca3e3fe,0x8afaa33d2ca862fae629,0xed8278e8ac39d1baa645),(0xfa88292e8cc942504909,0xa25a8e8884b5d95effe7,0x9eac89b5b050a89c958,0x16e29e9236c16ce555a2,0xd2c8da4f9f3b4efa5cce,0x6984030ab49a274d52c9,0xb854b1005f2f5cb4535c,0x84308c6d79271cab5279),(0x51967769afbc01dc31c8,0xa06744f96f97c3e42b0d,0x19c0a84b9a28137704bc,0xcf47ed7e3a82b496146b,0x1fae210ec413dff406e4,0xed0b87ebe98a805eb9f0,0xbc0a483a3859e0c31df9,0x44c4354e61ea96e42e6d),(0x6d6949f2a04e0ab6803b,0x380af6feba1def0d040f,0x5fcfb04662350433fb86,0xd430ec473fe6dc0d6681,0x929296e1aa674ead2d05,0x3490a63603b2c8d13159,0x4aaca6ed3bb180ded1ee,0x32266c4ec84840d0f757),(0xe10da67cab56b2b9c291,0x2be31c70524859e8b963,0x60039232ce0f3081c073,0xc250f0059370681697b,0x15d39594a473c5e42c83,0xddf5a35aaf8616e35c7a,0x7d30f16961a5c3e31415,0xf1290ab46ecb67017557),(0xeca37bdecd0fa05adfd3,0xa7a4b004f524009224fd,0x4f79d630a328385324b8,0x6c73c6d0011e7d8bf19c,0x56ac4d805e54ce66db33,0xba61b3a8ec632034b490,0x935f8f8e7dc4ef527d9d,0xa749976e84e4fed9aba0)),
((0x6f1c089c041d615926b2,0x18cbed46a38dc0044edc,0xd49211e1a16b4d1bd7f1,0x6f8884ebe50b0783930c,0x4b2375632008267cec5e,0x6714a1db8344a44a27d,0xcd692b5349ff04cb4c1c,0xb405659e54f1f23e1d2),(0x3d90f071fbb5298a169,0xf234210439c39bb0eab0,0x490b54ee93b6dc0e50e5,0xda22006999d42e2b0886,0x94a5c41d2a1e6b64001b,0xf59bf479d554ff070631,0xa44ead8429d0b38714c8,0xf7ef4371d6cae68fd9b6),(0xde3b037ca2112252d489,0x2e9a7d87a1aede5e964f,0x9dff159e6f96f282f58c,0xa521caba3534da227d15,0x4ff04d5c8257e46f9413,0x7f5094bc4dcc62896af,0xded43bf85f256848a375,0xfee5cd6a3cd6122c34a8),(0x4089f3a5723c22dc4c00,0x83a9a1143327fbb5d4ca,0x5fdf48c767f717e43faa,0x9b55277736f464d604d3,0x800082a7b3325f84ba0d,0x6683b69d551fc7637978,0x66cb55c6630b53ba2a46,0x6396f0645e8d4f76a32f),(0x92697cd4479bd6a70e20,0xe0fe2725d53440279ccb,0xd18ad7a6a9d72ae5af1f,0xd040938b9125c99a3ab0,0x3aa77c78cbfb705937f1,0x4bfbb70f3a6f8fea3fc5,0xfecac08a0a75f3aab057,0xa3a78f2795459226b4d),(0xac301722df6274828abf,0xf6ba6f10e656248a937a,0xe95e5e104d2770e8fcef,0xfdce58dfa6f578185eb7,0x50c11123aeb162ba53c0,0xba8ef4d408d08254b54c,0xe1ff83d55da569534501,0x21817094d7de3e73953),(0x4cef3c696ea411c3f88b,0xe51aa1332154f03e26a,0x42fa17017e78546884b5,0x676f01fbbda1b437fb69,0x4ea65269b30dd4b98310,0x5b661b3aef478a2eb773,0xa3699ecce166b83e2fc8,0xe3089a6771b053eb8ba7),(0xc542f589e02aef88fa2,0xfd3a8d515a1c824d2a81,0x56ebc7c7eaea553c4131,0x5df1f15d4e1aae276452,0xc85777737b2f49a57315,0xa3a66a611ce549b0449b,0xb116fe0bd45c76ace2df,0xd68fbf2dfad060911016)),
((0xe439408c9da11fdfdc69,0xbc5d79c8855ebd591c1d,0xa2b4b68e7c5cfe8f0964,0xd3035fe9948300fb9153,0x9cc4bad7325cb687461d,0x4e0b2c017cd8d5977ca5,0x3a4afd13918e157775ca,0x485b988e4bf50f93d13b),(0x17502ab4ff60051a82a4,0x95e58bb106781bfadc98,0x3ba7f1cf12c2218d04f1,0xa7ba2a364c7f5c761bb5,0x99b314c0c702e7f6d697,0xc190a0976b94d4b47e2e,0xffe72309de66428ff1a4,0x70a9d0bf75af926499a9),(0xfeb53ff71a05a8693d1c,0xc7dde047f376e0b5862f,0xa09244069064d766a1bc,0x877d9baf14ae4c900d95,0x94656b97a90c7799254f,0x40f1461ebecc6f24f5a2,0x2d63aa6e55b1f432c605,0xd54dbfff8ed35d069de2),(0xbdc206859056b624b9a1,0xce7cf154d8d0ab9031f5,0x1a6e38cb5be31b179efc,0xe2d16b936bf8f6661df6,0x503533dbcc0c0103ff5d,0xafa34a7c1dd4a9549f4e,0xcb9f861752685db35e63,0xc230d19007d6fa7b2782),(0x19ad9f8cf45f06c30480,0x1dfde4a42e5eb22822b9,0x16638795bc448dfef693,0x9d01ef4947e6d25834f9,0x3dd12ce531beba7a888e,0x39cd88af7c26bf1dbdcf,0x3b99e09c5b90125579d8,0x43aca31647955731c9b9),(0x55cbb19a1dfbfe4d76de,0x8418852670b7481494f9,0x3502acdcc7b96504c8d1,0xcbcfc5b4fea1d731150,0x78c5b51bc8341c2785ff,0xdc912f3581edef07b956,0x36cc14fc20a030be2ef8,0x34dd8b023bb10383000f),(0x29f3dc1e84b7a2cb9d1a,0xb416b1de5867b0e9c17,0xbfe062be9d3c10304462,0xeed63f689a1adde38470,0xc8c22d9514fe6d7fa635,0x1d86de50e72397b12e6c,0x24aa8cf0e59a11ffac5d,0xcc44d88d1f77ae1dd6d6),(0x559cad03055c3aa75bb4,0x6538c02a21a49e89c8a1,0xc1c131a7809da3822d33,0x95577761650642213d12,0xb6ebd1a8ccd1cb16440d,0x9a6b0299629cd6dba31e,0x3169c5c69e1126bd3d8f,0x82ae0c10956364e19e64)),
((0x29500b792e0bc332a990,0xafc937721eb0023d7159,0x3620a5a63cd5e939c46b,0x69ebaa0e257608296dd7,0x46c12845bbf0c07d16da,0x7275c53acc42caa642dc,0x644eafa02c8c88c0027f,0x74e30847638fdfd998b0),(0x17c3ba6c415bfd432c90,0x6246ea7934e358150b92,0x79e8a18ec2b8f349367b,0xdf64b0d2247dc5ec0e50,0xd85e2adbabaaae4066d6,0x3348ac35b768f47e63b4,0xb5b00547b4c003e88485,0x3ddb9772f69b5ccdfec9),(0x11f9b8d2cf10b99f07de,0xed406331abfcf0c97bd5,0x5063e1a5ecc63eb583fa,0xe4047ea451e1144e5d51,0xae1f6bdd48dfacc674c5,0xff5a6486743bdcbcd7e8,0xa6b49402ada978052f88,0xf9d3931abe6f5dbfb6ee),(0x86fc31888c0a940204d0,0x86ada8749f8ae0ff7ad1,0x479337248d898fbc9452,0x49a524a65c553809baeb,0xfb17120d821fe674ab52,0xcf02c863205f3f47da89,0xc02b2b56d69a022dfd63,0x306a1f5c719a65f99e34),(0xd1ebb94d9c602eb864f9,0x6756ea0f04c9ba89f7d,0xd737c8bebe866f9f9397,0x30b73fb2d283c5ea3318,0xe6fa339b8de9e4584192,0x56193234d6c1e6049a81,0xaf4ff59e6cdbc710caf4,0x170fd0c25d950a5daaab),(0x43a983c994cb1b55977f,0xb71d782b78960965e364,0x4ed7ebebe42c6d83f7a0,0xe45f134d658ab8db6bef,0xcdd424848b6138c7ee87,0x47248eebdf27e845721a,0x21004ccbc7380329381c,0xbbbdb52174f4360a0955),(0x6830cea80c8f18c36682,0xd410c719ada2dc37c249,0x31c2617200576b0ba5ed,0xa7746aeb06e1dd89dc8,0x32155446c76d5b4724fb,0xd633acce425fd2b53b5a,0x3749df24dda3f5e5ca93,0x7a8fa1b10c3d299985df),(0x14df54e9547092bd1c32,0xa0baefd57a8304cc13c0,0x2e64818252a779bc8af1,0x9db2adedf96dfce7a6b4,0x2afa7d52e24421305d88,0xca7ba6dea6a8e8930fa2,0x99a52859176d47525f86,0xe6990a22e18dd4b09c50)),
((0xfb43c8bba8f0af14d50f,0x8696327b6012ea02ed6,0xf38c58a237944168d8ba,0xa77d2d4206f5c94f4cea,0x4c8fd0a70c64e91e1341,0x7d470f5bcce90300f18,0xba9bd5d2cc1c395bf644,0xa7fa2f6fc601382171db),(0x373225648a0edc6f0289,0xf4b171ba3389ff14f4ef,0xc8920e9c037660f06c04,0x68175db81094766eca26,0x3306755b7d356683c23,0x6598e5e40587ef50c7a1,0x276a74e11d786a019016,0x7d6eec47d9660b0b6536),(0x8b8c016f8e372a18b673,0x7271b1e1fec40164e8b4,0x325917c7935906680b6b,0xedee56468ea9592f3575,0x3e662643d93cde37112f,0xd3cb7c0cef7312d0c76b,0x78cdd1fe83378d84be8b,0xe65373dd88bbe3e6a2e0),(0x9a285ea4206bbd277cd0,0xdc30da21373b37656506,0x51803695b1d6720ce27b,0x6deffca3de3d8556cf45,0x830c1b6158500e361e07,0xdbb70a242154527609fe,0x23d85a47d434873079b4,0x7cf1d398875251c031e7),(0xeeeed4aafacdd6cb9b89,0x406cc60ce905e012de06,0x548c12ed87886773935d,0xba002db26eadf8fdcf39,0x84754ef968cf8e7b0b4a,0xce080a3e88e6cf90724e,0x99895140e9f8b3024e90,0x837fd32d980ce465aae7),(0xbecdc5f6a4c2db36fddf,0xd6ff1fb7e1f885d7b8ae,0x8ea96c3e928940e693f4,0xa0f6f7f33f504bcd7fe8,0xa01725568fa9ebea4c0e,0x81425a763da7c0986b1c,0xcc17f91555102c5fa650,0xe1912295da8cc0c135bc),(0x8064a1d08ff75ac5eddb,0xa9b5844d5b1e1f53e186,0x87a721614c60cf1cd2d3,0xd5040ce272524f775106,0x7ccfd113c551d9043789,0x3d51a4bd74328f204e8,0xc2435d8e9e0b8dcb7b9f,0x290e02144e6614b373f8),(0xc185b96195bc2d404d17,0x86c174055ffec731ab6a,0xd6f86832fb5060608f1a,0xf3184f02898082c02a0e,0xd4942ac05bfb6f8dc23d,0xe3c54ddb11a0aab9f283,0xb4c31a0da6366ffe7dcc,0xf8cc35716df3a7adb321)),
((0xfc0264291691c75f47f7,0x28bfc4f904655e5d0d33,0x87b2b56c7e43beccf6ac,0x154aa0e5d036893715c5,0x6bf587fbdb525a0f72e9,0x3b91662fddf98c634e5b,0xb06809990119fc7474bb,0xf248849bb6a379448101),(0x1ef7b4aece035ef3f70a,0x7046c0408824b2928151,0x2e28a2c9f33d705f1a10,0x4d0f1ddf0cc49e79c44e,0x694164b879fa602d8e8b,0x7953a419c0dd1bd6b18,0x66b1cc7a70d9d9152e16,0x44aa8c3a8e202711b310),(0x5be6dbfeee393b89717a,0xbb3a9c30a67d511a476d,0xa4d1d22d50bcf291be6b,0x5668c3a978b448cda08e,0x163383fbf4c62da59aa3,0x967223e9fb5602f138fe,0x4921790ccc12215966bf,0xe505738f9aa4c70eb340),(0x53ceb393f49a70feec59,0xfad21672925435709987,0x613a329c36a9db5c5a0,0xc4b345c89d53ff5cde6e,0x68bed51df336ddc5c9b9,0x2dd9ff23619f798f1955,0x298454a4beb5f4775990,0x3b61ee1f66392f6e8023),(0x2dc4515f06d3126e4c2d,0x24a0f0748c6377c2ac85,0x6907a841e6747f0fece,0x465a9fa3f178d54717da,0xb9f655b8b0ee3868b74e,0x10c3cf211fc28a6b063c,0xeea5b0cfc15e68650327,0xde590e6dd2cbc9468cb0),(0x8f1c3358b3fb32319ab0,0xfbe9ccba3ceb2d1503c8,0x97fb7347602e6965ec05,0xbcd473fe3bea500272ef,0x6e7e4b360836f92cc390,0xad74dac9b3f427296d31,0xfa0022883d6c7ffe1aac,0x5c780f18248820c467d5),(0xe3a33355632784193e83,0x143695edad5253300e70,0xcbf2d35be9f2bd5e8210,0xa10e7347a46c5d9d1c6a,0x7d88dc3cd45d3746fa5b,0x8f8fa8e1c5599b948746,0xf9e37148121138b97a4b,0x27c7d9640082b447b30a),(0x8cde8044e269f9c4d4a4,0xc183f630e799708571d1,0xbe6a0e8ca0d65d64cd7e,0xc2b24b2234a226541d5d,0x18ff9ab62129ebe306d6,0xe7cf5b93a85b08fb09c1,0x8ba7e60d5eaf95c5d3b4,0xdc88d7c41366d6f2e2e5)),
((0xd6ada6312e434842b0b2,0x68da6479a73615af27af,0xea2c355def6171264ae5,0x36f4580d2047e46ec524,0x3c468179d43555e09023,0xadd0cea83d4c7c3dc4e2,0x5aec2b2379fc18724c75,0x27ef99204da51333754d),(0xe9228b71089583c3bfce,0xfb944eb0fec3161e67b1,0xd054acf249896908f603,0xb1bde53fe7b0d43892d2,0xc2ff254bfa46ff698ce9,0xf2903dd0b26ec81031c7,0x2fabd51ec5e4de5c42e7,0x7f3b3687ccf813756d1e),(0x3130d8de9ac39aa2c6dc,0x5459eecb6fd6abf87ad0,0x5632613c93936503b9dd,0x67d43786f71a8fbbb3c8,0xed981dddceef48ecfeaa,0x863fb138789c5ac8a9ef,0x4cac7af319687cc4cce,0x69924a34e5be2ab3cbc7),(0x26397ace45c8cc687ba3,0xbd40aa06812f2c08d5f,0xc0660e42329bf9e2ccbc,0xc3b1134e7ef8fb7ac3e8,0x70d3db01474761ba4c2f,0x91fd8e454685e8a384c1,0xc5eee903bf2bbe71902b,0x1f87e0c36ff7b3d1849),(0x2484067496530c8dbdd9,0x8bb178f2a15702c58728,0xbb9c897e9f14f10a1b2,0x623b3530238c6d874831,0xa2a7e9a6879d0943e550,0x25b825f980611f24bd4f,0x277726e741b0fd47647e,0xf09e6e84f18193ec9ecf),(0x347761c97cfb8231987,0x4bb88bcbcc2f6d90587d,0xb208334a8e9f51e7fd0c,0xd0412e923a8c083ffe08,0x7efdf53e36323acc7ed5,0xd711c040e0b21c23f4c5,0x985e3a95adfeecc829a2,0xb97adfc5fcc1fd9e4128),(0x959de98e6462233fffd8,0xb54bda4a301d1b2416fc,0xd8f619cc0c321338e766,0x93a481c680e5a1de996a,0xfed9ceb233101514624b,0xddb2360ec47801693fa6,0x1311c26087e667bd1fd1,0x8f2b0c99c4a56778f3be),(0x8860edaff6d15f543a24,0x19adf77e35676820aa4,0xbabaacca2cc50872220a,0xcb8feac8b4effedfe24b,0xcfe53ba240f507d7dd40,0x38b1e81ff88e1be3cc01,0x6692b94f2c951b4bd910,0x6dc0616ffb482fdc94a5)),
((0xca85bd427c19eb1082f1,0xce33b01c14e5d8bb39dc,0x48abd45ffff0681b47b9,0x76c676823fed1b917757,0xf9915e6c886eac5cdd5,0xc660c947390501e02afc,0x952615c079baaa9e5f2d,0xfe5ff2a2ce3887570d7b),(0xf87d560fb1ca6e1ae746,0x3d8ffb0ce7a51705fb16,0x1df8404cefb242a2d22e,0xb4977af818b6cedce00c,0x33846a73bf399fe9c5c,0xcbcb83c8211a01ee2ae4,0x4cd2d18b4f79dbbb7ff9,0x6e524c5b3aaf916aa08a),(0xa065bb0e2a5b4adb58a8,0xd3b8d73f300a855d1c09,0x26bb55b9ae1c30a27e3d,0x5f18e134fed243c91b4c,0x6ce9cea4c90087072db6,0x42465d73d65e9890de70,0x29d337117924ab3f0600,0xe92f53bc9cbc40f077b1),(0xc58863e16c05cb5bd6e6,0x475d69682a5b9320d344,0x7f494143644ef904624d,0x2265aed8d9901bdb5bd7,0xa7cc28a9ba31cecc835b,0xc52ea45070e988bb02d8,0x78987460ce4a6f788a43,0xb4eacf9b0821dca4e42c),(0x1f84ad1671817648d271,0x18c64a19a1d685c754b2,0x676e81d832c4e5027dd4,0x1041a4d001ea8c01535f,0x5a3b05f24c7fc084ecdf,0x9f50a2a6f27e5f088993,0xe9bdfa8396fb6253e383,0xda699ed9d3a1fbcbec08),(0x23664f15aa9d30179db,0xc78130313cacb138a64,0x875171dbb7e31123a3f0,0xb22e0d1cae7c921b414e,0xe39daf8109497f64e64a,0x51ca86faa7520f2f9039,0x60805ef5429521795ca0,0x7649ce8d2996057ad3e7),(0x3416248ab2300d9ce6d2,0xf53bf966e6ac30160c62,0x9e3dbd4062ecb05d4fea,0xe620fe9b55932f5daf34,0x35c8aeb910688b5283b5,0x90d3a8db7f3b240f34cb,0x4b545b66ca02df4f93da,0x9ff2c4f57378f7fc344c),(0x15ab423b26050b4a3211,0xb7f11760efe9de3a389f,0x64a383393b6218443bb7,0x9f2a594303194a03a255,0xa9206e5596b58bb75706,0xe40f69fc430e8846f860,0x2f0e75042d515b9c99c9,0x41696208c3a7a7c4e052)))

def page9 : WordPage :=
(((0xfa6c48726eba202dde67,0x679056254301e4371dca,0x77db2e9adbb4369eaee1,0x3a954c26448f1d087605,0xc826b39f84272926bb9b,0x23d1abbc2892ce7b7fbd,0x66011ee0c31b3f926680,0xd544920d333e831bfabe),(0x67530f41b64fbc0e4310,0x4b9c0c5853af653ec079,0xc5be643ae988bd820369,0x40a9cc49be542f5c13a2,0x9984a8d04d9d15c6d9d3,0x42840b5ce4563dee1bca,0x9aa7e23bdfcff2d3b373,0x3d8fab07366875dc5c0f),(0xfe500cc15eab7fabd9d8,0xc88f86290ae4638df33d,0x36f15849477930854e87,0x99ecd9f4624ed7d17f51,0x3087ff3eead9bb9e34e5,0xfca1f7543cfa7ed203de,0x37023aced6be954b4ebd,0x30172d22b9a98a468ab7),(0xacd9f2f485b9c09fc0f0,0x75aa4beef4331341a16f,0x54fc2069de9727a1baf8,0x4189c62e0ae8c871651,0x8379858e5c0434600373,0x8a50d91d5d70bf9e6d9f,0xda9e30eef1959a86eced,0x284f7a448ecb87cb85aa),(0x2c012a0df011a5d6d28,0xe9cda99405af43b3c773,0xe16ed63aa1ef1d0399fd,0x8a8e8ccb0dddb59775d9,0xe5014d09297f8ce327d6,0x53bcf3946dfcc1da5045,0xc4ddaf1d181bf543312c,0x976ab354c1b00a7988a7),(0x602d974a33feaea5885c,0x1666f88a18af6247c4eb,0xbe9ac8eff1c1d3060517,0x9ff91885a905675c8e85,0xe5323e8131f52c41dc1b,0xb8062ecbc5fdf0400c3f,0xf094efe4bf1fd87089a2,0x68b456ded652d2a407b9),(0x5c9c58d8ab29b0656567,0xc9bf2a413646f4cc99ac,0xb8ba898e0415a4ecd425,0x7f3ce6df408cdfae0318,0x430197768b08367181cc,0xe5f6899d9379d8556e82,0x9ec051711a08c9de1c83,0x8fa24040ce297204c0df),(0xe7de16ed68ef5f13f170,0x565291fcbcd4f71dfd18,0x2dc8c67f04e2b1a97071,0xa34c65814e8de172a4c1,0x6432a49de0dfb15559c,0x2821d10f16fb2d6080fd,0x798dbcaab684ce6c81d2,0x9ee99dc7c2a03c93712d)),
((0x387b11dca26d2278e49d,0xeb70a411c429f37c1ee9,0x74db652c3dc524ce1728,0x7bbb0b48bf1443ac92f6,0xad15c4b79678c4ac756e,0x2c9ccc365a8a080b5a26,0x22a1ec7ba2690d03c8b9,0x9f314bb0956aea9eca64),(0x31588da9f801dbb68f5e,0x5b7220010eae5547d5e5,0xb11e2d8a7db57a2d7604,0xa54dc83e0fafbdc8ff9d,0xe1360b6427a8eed0b178,0x1d6fc942855e2f0699c0,0x74f47961ed82c4e26f8a,0x706bf3be2acc7a6ef27e),(0x4ba672f0e234a4eda6a,0xe455389c264e67d144d0,0x9998c532358b46104275,0xeee940f544fac4e3bbcd,0xb00d50898354c49d5932,0x5bfdf788f8c0e8b4600f,0x9f496f10183eb3918442,0xe043639e41c2da4b3f67),(0x690fe89f8efc41252918,0xaf773abec622db1c7f07,0x4fde47e56c8c2af32dd1,0x61942689aa1ff7b18760,0x57398b82a0ce152b99d7,0xe4b735f41b22013b1f5b,0x4724f0aeac8ec774b631,0xd2294ba573e87cc7c5c0),(0xf664da8740c7a693f4bf,0x6eaf0de0f056efebe9f1,0x5acb541113e0360b148f,0xe5f69bfc80690825ad06,0x6c8dedfd462e9061eac,0x9937b8ba6fd4af3a69b3,0x180584db29e23ed3c590,0x25508201e577301a0df2),(0xe046f31d01654da60c65,0xae9137cd9af1aab28ccb,0xb027dd2ebe203712490f,0x961741c21f3b11256627,0x4520fb5f377f5f270450,0x71402bfd922beb4a536c,0x5bab8c259463953e4979,0x12275bf0428f2632136a),(0x5404ced373993d196308,0x9ac48bfbacc34d80187,0x6c8729fc2997702fab80,0x940cbc8979fb71447f6,0xa7e3bd66fe58628279ef,0xcd418d5cad8273f31fe8,0x6d5d1e936d5ec80b9bfe,0x143b28a74d3e6d837f13),(0xf016ee339d8e6abedd05,0x7496ffed42eb8de9a398,0xf677633f7cd83adbb06c,0x2e06a9bcd259f6cecf45,0x84af142d85fd8438cdcc,0xe1bb480e126aeb3edf57,0x652b280309746cb9c3a8,0x67b681c0d3aedc127c99)),
((0xb8e1b79acdaeb2fae860,0x6374cf2ab1cdcda98407,0xc141eaa009923c6feeb6,0xcae9b407c006435657b6,0xc2f4d615ff7b038ce142,0x7ea3dc3b57d07b544a5f,0xb46e5ac1345bd8e52255,0xe26122c43449e19bee4b),(0x6141a3d3b3e0db6dc629,0xdb6d8ec38ff9ee32999d,0x3b6acf5a938ee82dd56b,0x3b4bf937759aaab90f6f,0x88313ad005983b457038,0xf463ffc462715b6832f1,0xd22d3a5015d8d22e2b8c,0x2164520c875013108d18),(0xaff5eabdcd1cbb140319,0xa6d755aa21ec57426549,0x87f0d0930dbc4b21b3d5,0x36d8f6515ae4b1a2e9ba,0xd4e6858ea16f98e03f72,0xe2a129ffb305af2589fb,0xf5ed1454c4a64f6a2873,0xd87362dd37ae658a051c),(0x48d21a87404fb30d7426,0xda8a2267cf90bb433471,0x7dc8c5964c6ced968e7a,0x59b9662764bf4ec91b63,0x3f90a8dce4fc32179c6e,0x698963e4a1ea1bb56426,0x38434abfa97c66a85fb9,0x93d0b3691f12a4f1e6ad),(0x655f8f9adf42fffd246d,0xe23eb9c98b05d00b75fd,0x615f86b8b5d9513bf970,0xdad431b9d97a19456944,0x756f6e2f93b880000fea,0x3b9f5dabba1cc251c827,0xc41d99dabe7ed1924714,0xf4a184bdc56d5dfca659),(0xcaf7339bc024dd72280a,0x5542abe3d723f6cfd2de,0x228c4348e7743f4d5492,0xd0015472ba724fad16bb,0x274c6000456da00f9403,0x1c54ff5ad72c4598c553,0xe9b3e62cf2e52c981a96,0x28c4d1a63bbecdcc9bd8),(0x368439d3f84b0ff9208c,0x1c17d6a11a697c9f694a,0xd02260fc7f6b7c342340,0xc51d90044f8b1f61e737,0x6a6b8a3be9d64b06450c,0x7ee5b340cd0936a4d2ff,0x74903b96951a7c7ced80,0xdecb2ca29920ea146ac7),(0x53c28467e30a91ff3b67,0x8c81b40b03b673bac176,0x52f2b6bed93989d69d9c,0x1577618c1d479eb35ba2,0x121e40e7604c97d9822b,0xc04a49f8b192e34663e2,0x59264d65acfea0d34457,0x1cf0d41e997c292ddd69)),
((0x1e95f80179cb9b7f9a10,0x7ccc147e9c7d57002914,0x99ef82ac64f91d182254,0x109fdaef8cd250ffebf6,0x739e3642bf48e0c632ae,0x9ee14e703a95a2fd221c,0x6a2d263a3346cfd7af7c,0x5b248c62ec48a76f5eb3),(0xe20b94bbefc77021641,0xba94c70d63d63aeca8db,0x1f78e70aba7e515014ee,0x135fbfb5e2266844e7d0,0xf4f7c7d661f2c2f90ead,0x13fa45a8ef0dfc936873,0xab8384a49db655fc86e6,0x8e5d2da0d31b77771e3a),(0x571a513d8e2e2f01599d,0x83aa9613641a1c77a41a,0xffe1cc9b34147d2a9cf,0xe9d45e780c273e98795f,0x549adf9336b1fe9bbc06,0xa0aa6b066cb301441dce,0x6e79c4f1278f5037f930,0x4ad10915d92166a498e7),(0xe86bbc0542e1c35a5c01,0xb65e923f413bdb027dfd,0x1fed21eeed3fa8317e6c,0xc71084d6e78385c1e72c,0x8b675d443e78489347a1,0x91994de669a8096fb977,0x6154ec172361992335e1,0xa1750e42e24dbcff00fa),(0xfde3f77fbf41a1474950,0x935ade94c29bb3425e5c,0x766dfa3a748f5a056084,0xdc2164b81c7f2b00c5f3,0x7dbe542340621fdd9f6,0xd1f4ca87cc8f9a6ae8a,0x2beb1e7cc5824fe4e4d,0xf87cc8666d6ac8121e4f),(0x5dcaf04ad3d3438f67c2,0xb373994fe46c03029d8b,0x5dd7e95160bdcff1ac0c,0x940721c2b5a06d588e9f,0x9447a70a2d1002ecefb1,0x1538fe293c6ce121278e,0x9e7131c88e2ab9f27c0d,0x7b61c51e746f40357e3e),(0x292a44683c67a5267110,0x376977f1b20f9449d03,0xb5ceec4a3126911c9572,0xcde6e2c2ee6c4d812927,0xf238aa958a226ea667fe,0xcda008695196fdb60e3d,0x2ea5546446fcb6829b6f,0x11f548421058ddba58c0),(0xad97763d25ec07ee6d02,0x623e1b90e348b605ee79,0xf8ac3e9e9a2d37b2b95a,0x3908b2946876f9b108a8,0x500bc2a6874bd7ba65b4,0xedfdff7658347167e790,0x3561e1fd55d9c06d99cb,0x1d7ece072bf783b670c6)),
((0x143e0a02ee4b6e4122bf,0xaf46ea5d03527605f745,0xaa3b746d1e505c9df104,0xaf16aa5ed92c185b42cd,0x5e2a27d44487b43b9a72,0xbf674bc358df2f626df,0x92630d071a684f3b1f53,0x919d352502c9c53d3318),(0x6609d5b36980c39ae259,0xfe57cb0f824abff830a2,0xd834aac0e5d9f5ec1d72,0x7a52a5d364ed5d9d4803,0x2afce129430d1fc6476c,0x43d817cdb9f925370922,0x3e6ba74d47f2e1b8608,0xe6f1bdf1b6b4844db59a),(0xf04e911cbb00c8d4383d,0x70b1ced61406edaa9837,0x502a848ec351a64524d5,0x8dc546506f45194a8d38,0x437e1cb5f3938aa92355,0xab4f27a2c83352353cdd,0x6a99ee001cfd42348e2a,0xc9dc125a3bd6c4213752),(0xde71388f52b78601354f,0xf48c969d67da34062af8,0x902b984473056e280a5e,0xe36cc78582a9c1853c0,0xce7e00dd70dbf7f2a0d4,0x18424acb027e83d19f53,0x1118a39e97c2890ef2ea,0x26564ec2ad2a899e7d3b),(0xa2e45c2d69186076ad34,0x5f41157cc46627e60d2d,0x924764e92b8ab3e69c3c,0xe8b2bb033cabe90a27e4,0xcf2d99e9f049ca2df13b,0xe2b950bf3dbc7af68b00,0x7c0d7824278e02965e70,0xf5fd1550af438da26c0b),(0xfbf753330e7d13ffea4b,0xdc3f8bde2c65e92b19b3,0xf3d430e624233721be64,0x19b7d3f5ef5476856221,0x61cf15ef6552e825ba8f,0xdbe6c813983fb3102090,0x7ce9021794e502a03e26,0x24a7c25e1b696af76754),(0xc84b2ab39d7e3123881c,0x46d59e85e3c04605fd4c,0xe588c1ad51b5bad44707,0x360586c24671b08764e2,0x79ee88bfe36216148e98,0x9a7b7a0bd1e0ce411682,0x69174787a6256a934145,0x570a89aad3d64ade7642),(0x5f43175b33ec961912,0xf2ff19ac95cc08a1cae3,0x9487a896f67a8f6fed5a,0x82d0723dcfdb3d7c6de8,0xd602dbe25a4990c2ebd1,0x8c08512232f30189897b,0x4fc8c6049bd47b46835e,0xf2f32b85bcbdcddcef38)),
((0xd3d7e0d37bf414e2d425,0x4cbb991d73fa462303b0,0xf483ab7669790a3612c5,0x62e33c60662589396220,0xad79291eb69f8c3ae4f1,0x59dc126611143599c4f9,0x2490e452402a9269e5c3,0xfa81f783fccf23967cf7),(0xca1270bfb8623ff51e4,0xb1f6ba3e2a43b9b55324,0x352ebf636ef596be48d2,0x49c17112721d154ebf73,0x9907adaf0db8b1ec8a49,0xdd77ffeebf87c53ba284,0x118bc373935ee95d7779,0x6bcd951fccaecbbb44c3),(0xfc927175be6567582757,0x51b27bbdab3454276484,0x59509b24ab627affe7bc,0xf4d1c115e96b66918f0b,0x9aff196678506e996692,0xb4bbec3ca3bcdd6fcebd,0x627b7c0a288c887ffd83,0xed311a589cd8057a34c5),(0x639f45ab828ee8763947,0x694f0d3b5a87d644021d,0x68d268dc30705994d96,0xc3bf092e3c2653632c98,0xf9149473c4ef900a8998,0xfbc05eb71b4b6a664e80,0x6dcbdc47e103a9676eef,0x67c6a9bcf12ff8f07713),(0x967d9732b743c3a1dc82,0xe0e20700d6a45030faab,0x1afd27cd3bfd70442bc,0x14b071993c2b01c60110,0xf91aac47171598d2e8e3,0xd6faf30e1f0aa235a69b,0xf40aa4da4c1ca3c2d604,0x85bcc3fd8a8581d50217),(0xeceaec94ffcd1b490002,0xa61c0657d76b6b9cfe7b,0xab58674b235a37fd3ba,0x1e94e980671f93088da1,0xd22126b53fca7f4f9b7e,0x7f5b5df8858ff33d0caa,0x195cd2631b9b12e4901c,0xb841bc1f4aff36dff16),(0x62488aabb438352e8ff3,0x693ab3ba00c2651ff1cd,0x5b8d5852325d133053f8,0x9af080a172073f8eead0,0xcbbc7dfb17e5b6f2cf78,0xccd98d217e9d14be1759,0xd71aa67aae1c57abb6a6,0x270073dc25508b7c22f6),(0xb618744c29dad74cc191,0x967af4759aaacd64f327,0x41a27154f073d65a78d8,0xbc53c80171aad4ed48e0,0x3fd87aa79925ceed3b60,0xc084258018d404d4ce37,0x3cd7b816dcd63391a8e1,0xcf0838b58041c264f185)),
((0x550e8e0a226bcd9af353,0x4b2d5ead65fbce4cc8ef,0x9026839e29c80fb1d0ca,0xdcc17684cfd1c9deffec,0xd23400104c1f0896d34b,0xedccc1d3d4426715fb27,0x50000b88426d3b87caf1,0xac954f7d717ff70dbfec),(0x1e9b8b2895b1baa324fb,0xcd3bdad7695f875960c7,0x3234fdd785340c6511bf,0xfe409f05582455997ad9,0x399682f105ae3ed7097f,0x1c8732486fe5af71210b,0x7a72611d89c16dbb93a,0xf01cbedde00a4e3fd5b),(0x6872c050ae56f51d9ac,0x9d052e3819fda5f0ba7,0xaecef5b2495cecd5b74d,0x4944dcacb62045797b94,0xc654e8f649b4b140187d,0xc64a9db784ece3fdbb82,0xb4855b601bcd34205c9a,0x2e9a1b1ddfcb85d688ad),(0x82b3eb8e5801534c9ebf,0xf1e715adf16cf9c4a240,0xb2bf24a1143895317d3b,0xe4db6acea4ad627978b5,0x57d87e9c27bc32cf23ff,0xa80d2809326f065f7b89,0xfc732a8cc28858ca8884,0x2d2d29f1418a1b19b786),(0xd1d43ab1843d46117894,0xe00054041fe48a3ac2c,0x12644017c8d39a83b716,0xd5c73b69f00080a5b37d,0x6d86bf9c975e30994225,0xef1d8ec88d4408eb1723,0x80a3195b409da46eb656,0xceabbd79281b629248f6),(0x40247efbcdcb7a230f79,0x70dbeae5cc29714aab6f,0x7688eb841bfaa8cef74f,0x717cdbcfec9a7a5b4b3a,0x6b1ec89b5dd54cdd3663,0x197bd14c10b3c463c99f,0xd62de85249e98ba39832,0xe7fa5ccaba3e19116102),(0xd1a39eb500a588c7daf5,0x542a9167de95ff74c103,0x4d686dcb2cc7c1a0a8f5,0x97c55d067700400de70b,0x89167a11589a46ac1282,0x32523afe33a5a570199,0x8e226998d82394333565,0x1e1ced3367fc635eca94),(0x35c8f4e8cbd2675c149e,0xe9c7a61a5a5d92d872ed,0xebb55044b493b80dd969,0x107bc46df0a6eefdf456,0x7876735076e90878891b,0x54ecc6ea5acd4c5af777,0xc3bfa8c4a18266de835,0x67d6a9455a63449e74c4)),
((0xb3189a47c91b4719b28,0x576a4183481abf56e814,0xc3d33b6332262887e551,0x9d303020f2dc943cd491,0xffbd53434758a920d0f,0xa666f7c3b9d91b69022d,0x393311009a067e459b72,0x17e7e9f01b973d1ae4d0),(0x726edee2d968e9f451a3,0x649146216d47dded3334,0x181c61ca393bb72e303d,0xd1acce712472609e59a6,0xe6ce84efdbbeb40ab9b1,0x944eb46ab63893bf304b,0xdb1f08d28336916e791e,0x95b7f1925c26980ee1b3),(0x1f449ed8991d0d6ddca,0x1c4008775c00eab914a2,0x329600920039b8705a46,0xac8aec595ad8024817ac,0x1bcdb20678e50a7079c7,0x100c013ff206fc4c5f66,0x8aff76ccbb8c7bbf083e,0x50f792d1904287886591),(0x68c7356b82ae953cd9cf,0x4ba2ffe92fcff2f8b0d2,0xeda948e2ada36e1ba887,0x8b6351442ba469a7b678,0xe244b961af6c4e949352,0x504b502ee2fd49c93d52,0x952b3c35f4d8191a52d8,0x2e35f91f4468c31c6c45),(0xd08fa010939a5d9488c,0x822b4092cedfaa884e2b,0x70531c2f0d390778ae58,0x18070be0d74e39398821,0xe22d2e5edd367524f5ab,0x12741e541acf59483f55,0x3a35d8ccceee66fef887,0xe64f1eccdbf040265d5a),(0xab504c9d3c36dcee6871,0xa0d06b2884d4e0054aa3,0x86ab1745a1c2f5fc7a32,0xfb0e1e872a6ad9bd7c97,0x1e868899ba339fe81314,0x7803143b6f15352d2c54,0x99acb24992af6309b8fc,0x973b598543efc589375d),(0xaff7f5d14eb2479581e2,0x5ff6539af222232b422b,0xbbf897fbe62c8a2cc52b,0x933cb1fb2169abe576a3,0xcf2bb5e8e6b1b35c28a0,0xc14fd6ba53ee8da80057,0xad9d13b7fdce42208c32,0x4933064be1a09d98edf1),(0x183096f6933546a1c97f,0x6834f058b155b3260e64,0xbd35f54350cbe8e80257,0x2b95470fd1d9c754c176,0xbf25dba89de1cb6ce53b,0x72be6259f0287216b706,0x7116712d17576238da26,0x245b28323c192ca7db9c)))

def page10 : WordPage :=
(((0x83876bc0c0c06af8de7f,0x19433c829af7e4edf887,0xd42e37c1ac822ad86c35,0x4ff266eea98fd9925684,0x8a6c3b4cf244d8a22e54,0x5d37bf0ae758e5b24e2f,0x3139b4c18f91225fb28e,0xfbd57c21ba640e6051d8),(0x372af5d0c66ef1549e08,0xf7e1c40c154faa960c86,0x71e92b24b21845325f46,0x46aff47742b3013d2350,0xb576441fba1e68c5b5b6,0xc90912ef86ce86b982c4,0x737bbb7e9ed5d1406301,0x3a48a9939862f31900a4),(0x6a976c4cd2ec4b488ed1,0x4b01994491c2f2b5cc8e,0x8278e9e06548fb5ba7e,0x45cd9d2e10e88f8fadb1,0xc8ca65a5f33b086b302e,0x567df314283ea3fb756b,0x24e36ec4108b21b36e94,0x5ffe89a8bc9cf3ae857a),(0x6fa05d47c3848933069,0xdb756e0c659c177f6da1,0xbc0fef3043d8232823d4,0x2569a2ae651be846187a,0x4a5c15b530529be96acf,0x332c1faa9396eb72de3,0x47d3773261c51d4eb639,0x3595331c7288d0db00a6),(0x99c1145a4dc8761ea458,0x8eb9d9ef2e8cb8b4e3b,0x6379150db11a497a61e6,0xa9d4f4f184ed0b141a61,0x38e71f31b228309159d5,0x7a6abf62ed45325a4874,0xc23be3faa44ab31bc6f9,0x80e6fd5751d0112426fd),(0xaf598763696be7c3a2e0,0x97c52dc43b7e7382810a,0x90aeabfd943a48994b9b,0x214d071372c76216076d,0xdd9888eea0989c6727c6,0x60495595005f0172041f,0x61c22e32b1712e499892,0xf4885911fb245ca34435),(0x1c8b06be52bc2fb40cdd,0x5589a63dd460de6ec75a,0xad798be22ca1545cd81c,0x6274e95835acf86685a8,0x95a6cfc45e28c6a8e61f,0x69ecefee26ff950f0aa8,0xdd28ab8b8c3183e20e1b,0xd7cb0fe19b8bb5cf29d2),(0xa5bb105a4d69d07f4c3f,0xdc742f0c6164130565a9,0x5b3390ba4b172b4f9f1b,0x6f5248681b24d5ac7aa9,0xe561c8c38cc73f892051,0x1ffead8d72608faf3ea,0xc9b7a09ab9a535f72cac,0xc1d3d5d91e698c7d0971)),
((0x2f14575f78f6fbcd4aeb,0x3a68b0c37c58b39f66f2,0xe83ba8d052922ccb259e,0x8efb146bcfa331c58363,0xc992c9c23c13cb2091c0,0xfb1de22a153ef3a18361,0xc9ba90c28630d2af461e,0x43dae2e62e56a73823f),(0x3b0b71e2e50bfca8b1c3,0xa4d5bc023e08f56b1398,0x835e58c241ac20ffff80,0xaa5ccea4ee8e03697667,0x9de2b6f3f6af88d6fa5d,0xd3d7c5d16d74d055ecdc,0xfa460ce5023b0a0a6506,0xee779aa3c054070688d2),(0xaa8b3a501ce2e1089e,0x948a7bd9856100da6acc,0x4ca327416751b3ccf44d,0x908436a873e910e0c13a,0x182a1e7718186ccd915,0x8866ce1921b4ea3449e5,0xd5dddac8a5ad5b4d9a7b,0x791e9fda3fb279b09747),(0x2fe61c725ebeb8974c92,0x705408e09f2cdcd70f49,0xa645f2349bc24eb07281,0xdc2bae5f9a173c2dc014,0xd3bc6b82fc09083ab459,0x890222fbb48047f4885c,0xd2c97f04532a0ea0064e,0xd2a60392a25697814a56),(0x3ec35e732e954528e5ef,0xfa9c9f3517cf77359a9a,0x94897be584c26c4ef857,0xc32e59ab64c40145fdf1,0x45c5345a336300556eb6,0x5e54fa0aa8a30a07e0e4,0x9f74b062e67b97f82b59,0x9d8f48256958b53c4d3d),(0x6d10ec47c240393eb6f9,0x7ef77b73c552e1b80a63,0x941d1d9d687f5c26d16e,0xaec201c75e3d1724d7d3,0x6c14c2b1aa9d0d5ef2ab,0x8a1b24de0a7ff4563b9d,0xfa99463dd29e99df98e5,0x76ad8f67db66a78971b0),(0x9d919d97cf68662e1588,0x82928ee457eb68ad0b74,0xdb09c8a29583cef72f00,0xd72007ab747e2bd487d2,0x1908ebf4be53ad7dccbf,0x5969be1b84104919da33,0x286e1fc2f1f2c85936c5,0x2fe0263e4c9e573bbc7e),(0x75023810fafa385cf539,0x683a01feb939245d008c,0x54f12da064c4e721a1a4,0xbc408074d773a1b567d8,0xa56bcc73f77f2581a775,0x9473f5d76b01918ded32,0x1bf74dcd8d3d021a0ac1,0x2918ec1399c29773cfd9)),
((0xceb1f105e3c0baa85fb1,0x4bb45b79b4fe88efa33,0xb8620c676e34468013fc,0x92f267a89c9be9d2f3f1,0x8b606f42d21572fc712b,0x91f96451075976518da2,0xf922a281036b25e59fa3,0x9398f6452d7afbf87f8e),(0x1f1cd87c532e0e53e597,0x74bfe8e87d1abe64bb4d,0x90da723aa39baab78c0e,0x96a09da7557ba6be2a5,0xf0fc64a711433082ed5b,0x721d05a8ed94fa637f86,0x4d7e5fdabf890bb6eb39,0x26725e9b2a001a347be1),(0x61f65be2fc722351aa02,0x2b57038ba9f283404687,0x3e392752b1649314163e,0xa8699b39df462e11983,0x2810b76a195a3538cb9f,0xd09f96b06655dd010a02,0x166df67f9993f2591e66,0x24d229eee076b9093e9),(0x4102e9b8c62ce1d22e5c,0x12ef574a5edcd1342202,0xea66f1b3149a52fd009c,0xcb5f54b6649da19de70a,0x876ecc483e30e7440503,0xdddd759b64988b912596,0xfc45a0cbcececcc916e9,0x53cbcdd352dfdd8c9a7a),(0x55f61c6f9b94591677b7,0xcea9e878420c43999d58,0x57e15ec4a4d100940bdb,0x111831dc5d9dd35163b9,0x74a92d2744048076bf8b,0x1db71fef40e5351e299d,0x5561e3c8e35d77581ea1,0x18fc92077507ca2aa29c),(0xe17c932fd13554206488,0x71ab5175048a9a7b1122,0x76c69b448a21f74b2e67,0xba7eaa191a771157fa7,0x51e045c1179519a2c682,0xf42617592bd37bfdf092,0x99c85257f2297359b05f,0x176a4f3e1b84c60c66c5),(0x823f10e9815e7a29c65f,0xde822f9228dad413312a,0xbb03c282eb671a1278c2,0x160f48b33ab2936405df,0x432513ab28801cc2182b,0x5d14e6c10ae6b723229c,0x920968d78702c0fea35d,0xf3eba929b85ad98e6ad9),(0xa8ce46d9043d1c290c54,0x57580d8d432acf10cd9e,0x973d4776d3f20f307e97,0x51bc570efd64da58f02b,0x9232d9ec721609175908,0x994d6baefc0aeef1a357,0xd3e375ac7607deba8b30,0xb196a1b9c3a2c6a15d0e)),
((0x4aacf150229f0f1ad7c4,0xafce37bc47905bb10d42,0x6beee3270b2e1ef6bade,0xaa9cc4c49a010e8a1bd3,0x67df87887b8fd17e5153,0xe5437f64bd6a07177d9c,0x9c11f5c738c7b74ccd34,0x2d08162cacda0a5893f8),(0x3fe5c4a3792c65442b91,0x4130c2eef172f48b26cc,0x29d0db6428f84270741a,0x8d62d300aca964c1e4a3,0xb129ac5284f1a3bbeb8,0x2d42c18aef8d396a2bce,0xd6e31d03b82785b1728,0x637f09e2bbd258094fac),(0x17d45735e030668a722d,0x574a56c607ac0adf8261,0x2c839293dd6ced76734e,0xe10ecf1251551771c6b,0x6675e138898e140652c6,0xaef8089940350211a2e4,0x53ce919db16c919a9dc4,0xec05e746328b5e53aa25),(0xa3fe65d2e1fdd2d7c1ab,0x675c768677ab0830a86f,0x6bb887a5baeaddf62345,0xf721f4ecbd9db13239ba,0x7fc0dfc3e7109cc13562,0x761526690d6751b313c3,0xf1da9621681d1f77aa23,0xd756af065e0c14b448bb),(0x1c8a62ea8ab6937930ea,0x384deec31a493a39cd36,0xe43a44eb82a81d2f9e85,0xd998c3a12e1dd20645f7,0x88b3d562ea6b96c1a793,0x72247cde171a5a61be6b,0xa3eb1829bdc3674540d6,0x1f5858c3a1011634b9d0),(0x63f8807e153182f932fd,0x4fbd161acfe1762b04a1,0x561a7c2d19847ab44078,0x7d452b72b2e7c96b7ddb,0x3b271bde689d8b1a020,0xe50f9dcd1caa98a1229d,0x7ecd180a9505d420d,0x51cb6e3c053c1b896316),(0x20d25042e57615936598,0xd617ec2480120cd442c7,0x821ae94c7ac598e167f2,0x93fb0c723995b574ef3a,0xffec88e6fa08fefa1f4f,0xd29be0ad6333655fdd5,0xd86133f55eebd0d51776,0x3ad573b2c17bd339f27a),(0xfba6f1354b0989ff7af0,0x91c88fd2b958b56639e0,0xac1a84088083e852e8a5,0x8ec879e1d07a43a744c5,0xaa21480d31ee361e2b4a,0xf9e4dd2ee02e480e7b1d,0x5092479c01f4acc219b8,0x405f6e31bf9306a6cdfa)),
((0xd23264df1c948b76f031,0xa1a371cd94b056618a15,0x40dfd417aa3001d77305,0x57a49cf0c3453df4c08d,0x2ee8f8eea4f4037269d0,0xbc8de76d413f1c90f8bb,0x1af591513f2e3467ffdf,0x84c3a0e578d4b5236786),(0x35adf018f27efcacb5d8,0x79e781ba1126ab705be1,0x12f98366e7661ec02b7f,0x4d1304b1b455bd0e4203,0x2fe3873220853aefbb1f,0x878c38d46968d0152bda,0xb1c41e3b963c33f4c224,0x8f077c910d567bc9fd5d),(0xa2e87d754d8f0a7f1684,0x3d7107ce8bbb6fbaac3c,0x5c4d1ba4ed3332873301,0x12aaa3687dd0435f848f,0xf876c27a07fd4c7db9a1,0x67078e89b7d09627695,0x6a744f4b8911c8a97849,0xa0bec007f29b2b7235c9),(0x326b754a6af233d4681e,0x119bf1594630a4cd7285,0x5b9cc58f856e48103932,0x94aefaff4ec822f23477,0x3f8eb4ac24647392127d,0xc6530f165a3eb64a352a,0x8184a3ed904cde502d66,0xef7a139cb20458d952a1),(0x9da53931f591278181e5,0xdbacb2cec8f2231026c8,0xe2b26a6f602484d995fd,0xf6f992958eb2e75e3cfb,0xa34a6050650844af4241,0x467801191e00789491a0,0xcb485a061cc5c22e57ca,0x9c35db688371df461ac8),(0x14811cb1aceb2574e4a5,0x87cd61cd0db07a3e8408,0x1ceb4378757dcd4cebbb,0x24c21090b904893d5495,0x6d000408008e96b0dd4d,0xbccfe48b0f7fa9f66b60,0x954e166ba0f9c6a79cc1,0xc595f709067931bd865c),(0x81aa1bbe811f739ab194,0xab5bcf2a5d9640043f46,0xa082ca003389477aed03,0xde8c1c680b3bfb6cf9d,0xc34da4e802292f714f4f,0xe8d1034e2cd79564e201,0x5a8eebaececd3bd0187,0x131966bca45dcd06abb3),(0x74c3230b3dcc30659f85,0xa42c617c069c24d57d56,0xc758973a3525ed94ef6b,0xf34f2e244dd7f5093fe0,0x6e26b8f4e826c93cc2e7,0x86e83b4f629b2f913b22,0x7eee5fa291aed7d6ddc5,0xfba57c864cff7677495f)),
((0x46a8c51942099b6298a8,0xb96c62805623d29ea2c3,0x3922e4992d30a48faa02,0xa14e56dcff1db38f8377,0xf5a01ee55a17f1e99d0e,0x4cf36ccefb59ecef0fd0,0x2946dc5c77ebbe14d433,0xa6b301f85e1d12a6cd07),(0x268f39fa79e008ddbf95,0xe33a1046059071209572,0x429691f908bbea10b768,0x94e596f98d05bfc8187,0x804cca0084aed4677e,0xb016bc65a63a6f4f6f5,0x9995bf75edf7df3c5743,0x52652ee2e852fc25aff),(0x4d0f5b7af8d59d49f724,0x36e856ac319e59c017ba,0xddc9abba626fec610f12,0xf7cc642d41544e734d57,0xa18b6e795bb33587339e,0x9c9808e4d4e7129022a0,0xb73352546587c93207d9,0xca36731004fb5d450501),(0xd2717889356feb48f336,0x5e82fe5513fa098b43c6,0x930257d406b368d80a0a,0x85f1c5f8e1f522dc26c5,0x24f50880a226f69e685c,0xcc52d3b1d17d6ba6fbf3,0x6e29be44f83dab31d88d,0x7b7e14a4e7e7cdff524),(0x3db1ac1e626b4a802752,0x6d7d52146c44a7f69481,0xe9fef14e9a4de1874a53,0xf0613ddbb828b47db473,0x8380e47f265391899f4e,0x6175fb8e1b1e61a873bb,0xae8b991b6dd6c47dfecf,0xa591f3208095afe1b046),(0xc01b1a11bb37180e8eae,0x8699b36424fc0a7511e2,0xca963fb7868ce8431b8a,0xf3f8db453aa0bf4501e7,0x904bf8883e704b8e4ae6,0xb935cbe02c580cb16865,0xea38f953ceee00634bfc,0xdb88ecfdbd45fbffa9cf),(0x14c644c0f292ee8cba52,0x109163cab3a71386f48f,0x47b429c97b57c9051e73,0x72ddf2eb6f75a022f496,0xdc522d8a2c6faea74ac,0x3e4bfc384b153ca99c72,0x527ebb21a6d42153713,0x5985c319660b87b0254),(0x5679718b3f84e393d15b,0x3b92a0733a62ac3fcce2,0x9ab7b8f0b9ac7d3b8b20,0xfe9507c04b288ae00aa2,0x4b37cfea6a8e838b73c7,0x8e87416c2933062a71dd,0x73522b8245d30962526f,0xa3ee9387e37843f645a0)),
((0x37173bc01bc8619072b7,0x4d0384de87003e8a9259,0xd5c17c73761ac17b45a4,0xdfd24d5ce248096e52fd,0x64edc73064260d1b257e,0x9598ada32a7f69d94154,0x6e93a2d0660f71ace84b,0x24e4e7775192a5ccac33),(0xddefc8396c5923f0b0cd,0xa976675da1383953429a,0xdabcba6b8f65ff31c8c2,0x8a5a71032da5f715ae5d,0x7e6aebf39777ef247526,0x69773fa24484c9f2357e,0xd0db29b46ce53bed5e1,0x2fd89800cdb3804fd80b),(0x349fd713ac9645e410dc,0xcf6720285a21216e6a8e,0x2c809c6a7ba21cb61062,0xcb2cce57d70117ba90be,0x5e560307bd05163c5f1,0xeb073d5976c6405d0466,0x64c9bcd566f9c4e2d5d6,0x55e3bc7f49f09cc809ef),(0x2c91d34e50235c76033,0x572b158693db854c0e7c,0x97dcebf7114d31284c39,0xd25e359aa95c9bdbfe23,0xac5d123cb3c00154a952,0x90132b793e461cb0ff51,0x3b0d704f62053628b756,0x4f95221afdd8b2d520ac),(0x681591acac722976ac99,0xb2d0ea201e9fe9b16251,0xfb817a564ebd7e6295fb,0x31ef27b2eff80cb42644,0x4c58c8b41ffea996c888,0x766abdb9f2859cfba2da,0xcdc03e11810e7d45f02c,0xb51942fbaaa3d2e39851),(0xdda5123743128032e045,0x26d2dc54068b29d6c37a,0x99829f3ab6bea362cff5,0xa593243e60db6fc1b964,0x219b8e40002dd05910f4,0xdf00dce8f133438e02b6,0x1efc95d1d80b36b51ace,0xfaa4cdcb05ecb6685dc),(0xd9ca103b075ea49e6f8,0xe37f69afad158110e193,0xbab1ea7102b71fe13f49,0xda8105fbacdf7aa3c994,0x56c231784c7199e3cd24,0x884884f9e85dee5395c8,0xe725c98480ea0fd3a5b7,0xbe312ecc0fd1a4c815ca),(0xe142633002f5d18d3884,0x977a14359725df886419,0x2e7346f5461485ca6a57,0x99ead4ee1466176c5e01,0x8252656771239e6f9dc8,0xc0a9137337cdfb8fee5c,0xdda4bfc07f0287a29556,0x91439b8951657b20e7b4)),
((0x90f1bb71f0ee1cf51b89,0x5d35260b4c110b4a453d,0x8e19ce20774ed00e958a,0x8d58aeab82f372576b02,0x3c55afde819d09ba7fe8,0xe8d9d96215243af54dbb,0x64eb58f47cd3cdd8156c,0xbbc52646562a4dedb9b3),(0xaadaeb9d31f8e6630b2d,0x17ca1ca4aaae9885680a,0xf33aeccd4c376a30fcda,0xe0d6dd8c1ad091f42616,0x2289306417b16dd0e919,0xfcebc37c9a505975977d,0x599479182ad623187e5e,0x2693471d873f58bafa11),(0xc1864910aae4d757381c,0x2836d4388138b61fb223,0xa13ee0cc75175037f516,0xe426139c67e791e70b8,0x17a242d10db48526dbf3,0xc8f504e86cc478e9bd1b,0x4a9bcbf76d1f922e5a8e,0x8dadcad653076e504914),(0xf15df02fee2613236e36,0xdba5da1325c912c44961,0xc3758a4b11e7a3e89a28,0x4c61d87536ce3c3a3f6b,0x6c2276cd47731638f0b0,0x6e9f733496d81efb58ab,0x7e13217952659eca06be,0x60a83f539928e2098112),(0x253ed9387a2d733ae614,0xf903a410b2fe355a8fa7,0x238ff15883dc9585601d,0x8e7870ae85c9cecef747,0x576d3bec05a82a870b4f,0xeb6e7d2887fc53104d1a,0xdc6d7606242e8aef,0xa93e02ec82e9e7327f27),(0xd412dc0b66212c73e08a,0xe83e01ff768a95d8c94e,0x436c6ef1c267e3876f2d,0xa23e8f2da06658ada57,0x8815998833804e104cf0,0xc5f8042b55aeee9d5a30,0x8001da03028d3d52893d,0x4c1540d7096e72d49ada),(0xea95ab4c15080c560825,0xb2926347eedaac88b76c,0x3766d3f751aa5e78c18b,0x99914ecef2bafc274c9,0x977c71bec1c88301a700,0x2f651f59189b9e0a60a4,0xf4ead64df6c2b1af5249,0x57b0d215b79447859ca1),(0x75b209687ae054042577,0xd25ef4b204c1139a201d,0x839c552d623dcba6dc97,0xc56b8208e4e0d85c3334,0x55fdb801b2c7b3a9c6a7,0xd3c831c0d42f749dc47b,0xc7dff05e5279efc7c734,0x3de8cac31336596ba074)))

def page11 : WordPage :=
(((0xee0c695f9800f4ba0e84,0x36cb10c85b24d923004d,0xd130a84f845792ef9eb4,0x5d0bb4321009130838e5,0x2f6e6fcf3291c04bbed9,0x5bb0c9c3e22b2a1a56db,0x52f7e2b98038acb1abe2,0x6adb8558130f6a653095),(0x4693fce7139bd22235b8,0x46eaafd5c835bddb2b10,0xc5dcd92c16ecc24d2f0f,0xf74a0c1e03d7388f9ffd,0x7e6f258f0330624200a6,0x9e5e8f03dabd6a583a12,0x3c1eb2c028e8ede80e8,0x61cb097f28751ee066c4),(0x832b2b11afdb4af4a08a,0x91dd846a44a82137c678,0x980c599ce2c6a268a408,0x3045c316faa26d4185db,0x6d71408d72de48524c94,0xe887c5128c7b6cb5eb4,0x3c32d6dbeb69531d6e86,0x897002c998d0b043ebb2),(0x5371c4942ece0b25f789,0xb4cd79893766e5564873,0x28a1e90f73d4fc265e4,0xbc30b085500721f4b8c8,0x440ad9154aefe43a213f,0x9f745bde7b61a6d8e0e6,0x57a47369d7dadb215bf1,0x65ea08565cf2bad58767),(0xbaaaedeecda653df2992,0xb633ad26c61ed8d9cbd3,0x4e4f87502924bcbce01,0xc72cb8ac5b92fa09f04c,0x7f75075d56b9e232a5b5,0xbde8bcdcbae0b0e692a3,0xd12d013d1a81ac6f33,0x49fe95d48618ea331b14),(0x9ba591546e4ee7df624,0xa0975a23b6a0955e5f76,0x47f01fd6b23c3df58355,0xa8586b7263baf076878,0x8854759411a73887b9f0,0x4a8904e81aa095105bed,0x37458c775a7573614d9b,0xed4fdecbb839faebca64),(0xb732fc7e440fe2ec6504,0xc1618a3cb36d9442cbb4,0xb6ebb263aaee47eac40c,0xb8ccbf269c707c5741ae,0x316445264d3ef2356b46,0x4ea7c9c992513a55b7d6,0x8361608f3e6e58a289f8,0xf2924a9f25af2df8420e),(0xa30db4e3bc55379cabab,0x5b055ffcab611328828c,0x1cab5bbb1e6dcc8178de,0xe4e291ec7f2d9382a2d3,0x2a66b99880fd04126dcb,0x3d65444cbf3b322b2ba6,0xc983868a1c03ca51cd25,0x35ec5fe23c90919779ae)),
((0x4a97c9135a1c165089bb,0xf578d8d72e9628a1daef,0x94694bd5fb77a4fe094d,0x71c8b5aeebcdd6d5ab77,0x5138f3b5aab6d327a622,0x520b096a274b7f444716,0x153c9d17e5c4a3f2e007,0xfae7f2b2488480a48f17),(0x6bfe0daa1d6f6626130c,0x6ac59d98ffd54dca5075,0x18cfab8e8b95df22d855,0x56516c4afc95acf80ae1,0xf53fbef669a68ec25b6,0xdeb453d68ad42164fece,0x9986b8287ffec9c9e3b7,0x6929e900b23c6a15e934),(0xfe04b5b9258f86a290e6,0x1f468f83c05323e76c45,0x51b317db05a0d5dab9bd,0xb662608fb735ddf28cc3,0xc067ba3a044f8f62f362,0x5dc6f348b4e407dc4608,0x7bc5def92ed23558594d,0x42dcbc2210a5fa7e703c),(0xcf988547742e546d6ee,0x68c37346bcf79dc12069,0xbe1e352b1a55478d5ac5,0x626ecaa2f42fbbfe6f8e,0x6d14c1805c09261749fc,0x907fc2876326704b64cc,0xab8f00be48e6ce41f1bb,0xed2fbb4877c9f65c04fe),(0x736f8418ce861eac2eff,0x45aa410543bc7b93cb47,0x3bb79dae374043caa8ad,0xc239f0c48e7c979dd58b,0x66f2e86aadd489b2dcf9,0x7460b84a8e9f06e0fccb,0xaaf2195e93993f423320,0xb101d1a4179b2e2f7d93),(0xf7527241bc9830c8f1e2,0x5a02c6877d6d8f9570b7,0xd3ef6f85a09b6f8fba41,0x4555b621b9c5a308acd6,0xeffcedef281067263a74,0x3d83a8651293264df972,0x7a6de0f8543c8537caf8,0x849f0ba137a80654fb19),(0x261ca563037b9440e3c9,0x6d2a16d7a81396419e09,0x222d1f2d9e1b6c0efa68,0xf9dc2f05c74f9a521408,0x70c4f728e45ed0720553,0x72e0c06b65dcaea35d46,0x3f1eccca2ab0d09772df,0x4777272e5b98e33c7424),(0x5d87405fa8942bb6dc27,0x1121dd736550c085afdd,0xda740ce48bb146164ee7,0x8ee8daac4f60b9cf00b8,0xa6444b0db1510cefe727,0x38375094577a6e3ab01a,0x4e1ad5aefa5d984c718e,0x95b5b4a72c981f16705)),
((0x66e37780400deba3b41d,0xd61b0d5a96c89317bfc6,0xcf9161f1845e206e26f7,0xe64015c07b7296e37b75,0x97f0adf8fc8a7a7a88f7,0xf17032086963210636b9,0xbda013c9e6c124eead41,0xc3f2daadd6ae79943c25),(0xdcb94d5f9ba1b571e82f,0x605bbfd93561a1992554,0xa5541e2be7c7445f6863,0x43f11e1a4dcb4940fe2d,0x467cf15b1ce8436d9ee8,0xe3ff5f164081cf74f065,0x7678652205ef61d5365a,0x1c6b87e1fe6bd67a11e8),(0xd02518c93b1a4b2c9766,0x9d5b81ddccbc346cc227,0xaa1928cb4d215b5cdcc4,0x2aa65fdd62b90644f240,0x9aeb562d1a5e06cca7e7,0xd4cb53d63dc48ddd781c,0x272fa3fbe2944c42cfce,0x229a894a872bafd46097),(0xf0bcd58e3f34d5f22da7,0x7a9a6a5f6f3d19415820,0x29b3a671961314ef9fcf,0xbf1e4adf0d88fce352a,0x2907240984a7faffe20f,0xec310d92e89bf721070d,0x4f784a6db734a3727dad,0x9f56eac261a41d54ea10),(0xc225154631f03a27e733,0xe38b6360eaf74d2a190,0x3362560131d90019d95a,0xc9297dd1bbe9e4bbb7cc,0x2fcb70feeb5984f712ac,0x5b466a5d6ce765e21f95,0x9bd8ce5ec98ab5dc34ca,0x967f0e6c57dfa7aa2eb3),(0x7da041f1ce1d0b81af27,0x89b845ad76b3eed367ca,0xc106256eea28f0fcb5ba,0x8389d5c18a443cd9ce0,0x87a4c203d44eb5614c4b,0xb1e3760214e8b2a3466c,0xcf685b973f63798b53d0,0x6c5b1b0efe2caf22e8be),(0xee6aa794db4f876719dc,0x550254e11cabd7c603ca,0x92135e5f3a3a4538be5d,0xc6b5436fd2f034a8bce0,0x4b807bde7d4caa1353fe,0x5d8c6eccb1897d4d612e,0x2185b96f2e39b3d876bf,0x570672799d2ea2a7cdf7),(0x2b895fdc778ce03410e0,0x82c27f004356cbe45000,0x7bcba76e0a581e73d902,0x722aa546ebf7174d0116,0xfeb374bd23ece9757101,0x751b65cbbfb6a054ccec,0x84d6bcaf6be9d50633f6,0x71d637c11734d57bc2b9)),
((0x518dcc82febead75d2ba,0xe4051feff66b9f3174fe,0x6f0a00817a7b7e6ed054,0x200af8a0d1acbca465f7,0xbda0749b325439d56cfe,0x7229e8fdaea48eaa3036,0x1a8708c65fad06fb0c69,0x7e76b4e2e91e89d347),(0xc71e264cc5848ea2858b,0xae273de18af4b454f6cb,0x82377df1813638ad7630,0x33ce060212536a252db0,0x87a5ac9364309d24d3d5,0x2cbac60c2a29048ea75c,0x4f7efdecdfd61a93b850,0x2ae087a806611d9bd7e5),(0x477756fadad1fbbfcfe7,0x8952ef4fd78120426243,0xd2c1caf125deb69be50,0x541feabc6ae707fb88f5,0xdc1314bd1a31aa8aae4a,0x488396cf2e4df7750483,0x385ba22e92c687a181d6,0xeeb571c2e749bafd4aa1),(0x574ecbfaac9ac65aedd8,0x6275928d11eff96c7ea6,0x43374f85bd4fb65f39aa,0x92a6d12fd3ec22cc0b0d,0xb03f3fd101df254a88d8,0x32aa275016e0bb4189,0x29aa4e4d48ce0b945283,0x46c923fcc00651af0b4f),(0x9f132531575221a2e2a8,0xe38bde890a875cbc311c,0xb17456b667575d67b852,0xf40888fa0e0bd117552c,0x7d11d7ce59a0073b9ff7,0x4d517a35a9675f6cd8b1,0x9914edba2b762935e1c6,0x4d85b55617c342c7ca83),(0x2414697ad371674620ab,0xa91fb03fc89364fc5d74,0xbf4f47c559b3e309088a,0x8db057d2a941b74e4f20,0x3c2cf3356a9b0bf22b8b,0xeb3a65b677a640099e40,0xfdbed835cd00dbd8a9d8,0xf63134635c9207f6c960),(0xa0146cd035471ee338ec,0x31c5cd18f72758518b9f,0x8c824ead002380f244c,0xbcb979ee2abfda942a84,0xfa9ad397e7b4bcf6a529,0x650ae16f5bda1a95ce8b,0xac512f3dcd1817b214d7,0x101e12e0493e4980fc9d),(0x158948ca05a670d68a28,0xab4f1938ae0de836d58c,0x855f91af9557812491ed,0x6a1016a10295823fa384,0x2e9faa88a3aca90fa39b,0x5f8e4b912fc061e962b8,0xfc6708c95bda4cda0216,0x8d66db2250994011f76a)),
((0x589305115dc2a7a73b9d,0x6e1ce3ae35b15e2b6d9a,0xa547ac672ad41a9edc3c,0xea1e439adf2132a02e3d,0x81b2e4c9b8cadcdea67e,0xc87218a556bb95dace52,0x69cdceee0409c5ce6b32,0x284c0eb8746680b892dc),(0x74dd13a53e636b17a7b7,0x26ac8020c31a2877fab,0xb49995df78433397618f,0xa6081f7b0fea312414ba,0x6d085f030bf5d13651ba,0x26f2f6e3f4d5dd241646,0x4928114786f4da87c7d8,0x31e90174a0ff13486298),(0xc64d7a94cbaa06add2a1,0x91c3452d9616079647c7,0x7a8f5a8f06cebe1eb75f,0x411d633626ec7869ab6e,0x3faab3c966336559f2a3,0xeeac1936021578052d0c,0x40ca4170b0767111d999,0xcb60a29aa873ae39425b),(0xb82d6ac8b5f35a479360,0xd520883cd9f7ffb118e1,0x547007f0ac323963c20a,0x1c884f964c9f2ef9a2cf,0x545a3d3f200315ef34b6,0xbb5e46549d970c31e5c1,0x29850db61a5b4b801172,0x7682e8acf3a9f7dcb4aa),(0xbbee6d11f50ac64cb566,0x1ce8f2b575cb6f6b00da,0xa195994977d8ba418529,0xca999c41a5d5b5968d58,0x31e91321753127ad16a7,0x7d223cd2aa98ef181b9b,0x752a161fd647ea71a8df,0x5120decb48d4d39de412),(0x5b015d8173c7f9c20b60,0x18d6a0be4bc8ef33034d,0xa6e2278ef6f88e329f08,0x7ebd3fe8ed004d93ac5b,0x351029de23fafc4071d0,0x398fb3f8f84b41683c9,0x5a5b48f68c921cdc4556,0xeaa3163967aa63197d36),(0x129fe4a4b58ad48e6a88,0x97763e7734aafaa3aed7,0x5253fd45a1561bc220e1,0x4d05ebf3dfc467d90411,0xbd836e51aaf818f2d7f2,0x995884e70f114d15f9d,0x3c3619ed4e6d52eba48f,0xf7e07080f4532a3c5016),(0x822be2b26f8c03fb57ac,0x6017a9349b2e0bf2fb52,0x567668c0be73a58e3307,0xdf20219dcbc02536a2ff,0xa0ec41aae3234aa19f76,0x9d30c598a667d424ef6b,0x997da1a46f3258467e5a,0x1aaac152f628fdf4dede)),
((0x35d0ce76fe647ddf2535,0x16a1552f53ce06f1d85a,0xf1b9e0baafd897a594d6,0x8d29a3a38bdf98d4ab2a,0x84bc4e31bdba153b409f,0x8184653c6dffa308976f,0x222536c48d3e410bdc40,0x326e2daa3e57922b3126),(0xc8b37fdcdea8ab490be7,0x358a603c214e7ae4eedb,0x1016a5e2da7d83e2e266,0x31b2d306a595d9449f42,0x1894200d49ee017ca92b,0xbbe56c19a4482dac3956,0x91cd6c089989cf56dd4b,0x336415e7848e64ac8aa9),(0x697510a633486a7e7250,0xfa2de764d07b89f05b45,0xb0257f66646791defcb1,0xca829f6c013447b5e06f,0xa84394729fa51dd89b88,0x5be1ca3be7c4b81a831e,0xb70cfc4a818cdfe181b0,0xea5abbea5e8f6807e877),(0xefedf15671b5a7a8808e,0x87a786074978d9734685,0xeb057ee282a6164f3a4f,0x7c72429b43c1114ad812,0x29ac41cd5f21ebaff11d,0xf608525b2d75be80dab2,0xfd7600346cdb2343c91c,0x11667057c502f420f7e6),(0x671c533559e869ea77f8,0xddebe4741e6f417b9a8f,0x5b8e00151be675e01df4,0x3b7b826c835c1d355d02,0x2a0b615a40acb2aaf277,0xe263ab13acf822fadfe0,0xc629c387399ce23f007c,0x5a72d3a36c7242a2547f),(0x3f41b12f3b3ff6f91934,0xaf840aa6b231a07dc0d7,0xc0f6a9c04a476d65c6ef,0xdf3439059d0b67786b8,0x55db170ff42ee94994d3,0xa94974572bd51cf2be2,0x5d484ef891e7c3e2c675,0x98098d0bb608c7949d4e),(0xe120a6d44b636c3937f0,0x31f6765807fa46e3b257,0x34e3747410897f6fa674,0xc090f87146068349afc8,0x45a17effeda3534bd2d2,0xe22e9e2f86b9039a217f,0x78b4c848a0e7143b703b,0x748482622f2071aabf15),(0x295590d708fffb017133,0xc2bc51e43c3b081077d2,0xbb0ddf886cc7509807ef,0x633557efbdd5a5028f5e,0x759b25023cb3b46dadc1,0x792f778156c88e0c90d2,0xef5fe110e4696eba1613,0x76d936a7d6b78f726484)),
((0x61f053398a470cf4426b,0xbef3fda7bf6036f75118,0xe26525d4c8a5c78a1846,0xf073a1417415c68682b0,0x613d2c3e328e80c1118a,0x71f88ee0fdf6fe3d9a31,0x62a4b95ec9e10d95d7ae,0xddb5154c0be9ba47de81),(0x5183167abe5db1598fe1,0x134589e3e0351cb20a50,0xd0a247ea181a462810a0,0xe0df1b941c78c1a1bae6,0x153f028fd591bca94260,0x37465f805b580da63667,0xd9b1f60421ef64a817b7,0x8be21161b86a3fe943ed),(0xdfd7e71f86b1208bf440,0xed74a9a160be19941b39,0xf2c41911cdcf68217e9a,0x772f239c348606a23f0d,0x81cf019843d84b4d3db4,0x33e2ceb46d4dbea5712d,0xd7614fccdad2bb4b60e4,0xa94197c0025a77831d8),(0x6efe349377499a0f13a5,0xb309530a8cc8384a521b,0x5e450c586bb5031d5eff,0xa3a2fd3e3747bde87e13,0xa6ea81a47f52f8340fe8,0x3bfe43201178ca697b5,0x2b774c6ec7446c924cd4,0xc0a73db2e2595fbc4fcf),(0xa223f098c958e966e570,0xe02d59eaae38279b226e,0x3f078362b74ea9c626d2,0xc2276d5c964b169d36f3,0x5d0f3d2e2a8c75a2cee0,0x7e540409721f061821d7,0xab0ec0d9b2c07a3b66aa,0x525f7e5aea22719a450e),(0xc7eef9681251d92340a,0x1615d4273e60c253902e,0xc1d6977c3ecce637bded,0x3bc4a711cfd1cccf0fae,0xf4ff63bf8dcebc8a5e9d,0xbd8f120b8dbdc6ce4c31,0xb49be7ab6ac8873479cf,0xfb64c2df953ed0cd0a0),(0x98a2016cc88c61dcca08,0x9ca58c26d4d4f614d734,0x51793de163f731d3abf0,0xcc704b40c309f1fbf46d,0x72d3c7681f5701dc6f28,0xdb9f31ab8037c2ca5f3e,0x3d967cc1254c0ed4d24c,0xfdaa43b93ff3505b09e6),(0xd6b6eb7c6c1e78803ba7,0x72e87507fcffcb7e4ce2,0xfecb4b2482d72cb30dad,0x513d31cfe128cdd540e4,0xc69ea049b558d58c8f78,0x9b45c03345582a31d8a7,0x3d838e88cfe01cb2f207,0x7deb192e97efc286e733)),
((0x66c3de82c9668fdd8fd7,0x253c7a7e4ec9e7925ddd,0x7bedac9c74653719390e,0xbc0e2cf525823ea8036b,0xd306e4f6fd81f94f4185,0xbad42a9f22a10a33f296,0x3dc790fe782240645c89,0x84a45619523b261ae61f),(0x16216e76fd5094b42b2e,0x74a9be740f90c28c0779,0x5537d0b6507f14398400,0xa26e37c31d30711e5944,0x69da4cfd50fc59b702dd,0x3c0191461dcff7609937,0x2c1485c4fbc8edc627b9,0x7da91126867b477436b8),(0xc165691d273f2e479221,0x63cf4ee1617852604d11,0xce4c82ec9d267bfc6eab,0x9636a3fc9f1dc4ce51c2,0xec838cb3328d6111c8c0,0x60b8cf40daea1a1be181,0x426bff970ab4e6f80e77,0xa7c24baf330ac2bb3549),(0xdcc4c4311f9fa04e93be,0x12cb2e4f0fd4db32bfd7,0x3033649f6b0cb0b09214,0xa08095376e4c1a9c715b,0x198f83cc06e0e3808678,0xa478fcec5767b51dbf30,0x7696865df42cd0348db9,0xc9fc7a49db2c15b5beab),(0xeab7e38b28c6653b89b,0x4d1153ec9bfc5f249e5e,0xa9e3fcb155cd02dc9852,0x473283184366b4177fd,0xf8040ab858fc33fbf312,0xba3407b190b8fd9763dc,0xc4fbe047f9e5156e566,0xe1b023159a34b0567df7),(0x5b951d12b680e0aed909,0x27bad56f2e7cb0358dbc,0xb0032b86d7b3993e231e,0xdae20820226eb865f8f7,0x76ceb3c1d763a73dd323,0x1d7af16ba1fc2f6d2d9f,0xe611ccd80e596fccd37,0x86115fe4a8060255ce26),(0xf184fe54b792e80c9ea8,0x2324ad2219b0ed3244bc,0xb1ed2c9eab7e1f2e6ab3,0x925b3f07049557b3cf0,0x49c2df27aba5e70bf617,0x5e8706cda4a28a0deaa7,0x869d9b6d81c047be4eff,0xeee7c3916412af2e5fc6),(0x362bf5dc6d90c933d242,0xd54b79f9313964964dc8,0x12b90c4799dc8f0cfef5,0xa8961ca8718a394dfe75,0x3fdb0a450048358fae19,0xf1c054e26c488aae3fba,0xd81b1007a7768ed4e136,0xa582eb3eaae0e945f415)))

def page12 : WordPage :=
(((0x90c9d7a9ffd062d25ce9,0x8f09066edc9edd7f6e6b,0x7489e536e0cae012a6d8,0x4e134cbead8245beb96a,0x1afbd60edfe3cf5f90f3,0xf7e74dec884fac5860cb,0x312c9fdcc5993a53daf6,0x289ea64d442fe9ef0064),(0x1fe23ac63113254b773b,0x400b0c61758f7991f1fd,0x82c5acb74f3fa0e1be8a,0x25d3e8a0eb1f99a9ad7b,0x5bca6346240528dfbfe3,0x85199c78730452ee2495,0xabef641dece4b66787d6,0xc33699558f03d1e89597),(0x116df3554cff78839940,0x3a7e030bff021770a22,0xab6d4f349ab8c56ca79,0xcb2346b4054919fd6e8b,0x25edec88ef0c4a69955e,0xd6af87ff0f9380489a30,0xbc041fa5c4ff82984fa3,0x62bd12c0a867c8dcca47),(0x8eb271c47d409485caba,0x84d47343c987116a4fbc,0xc81147b665c10650419f,0x3494533a377c7f6ed54e,0x2daf0ee6ccb51672b2c4,0x817ee291f0f5300376cf,0xbb4b06679437c65c6e55,0xd406efdb8b5899afa234),(0x5585ad567b3230361e0a,0x76be6d9e56ab5af0c677,0x1181a16101b68d0c724a,0x30eeecb45b084b4c7526,0x4256995ec5db567c0500,0x8c23a86b72a548154ddb,0xac839be0e8653be48a0,0x5d62cba395a22ca56499),(0x80aeb2c5a34714b5c141,0x9fb3d8e0a768336b41b2,0x3ae738bd509a754aea9,0x6d93661e8e1ae56c69d2,0x1af263b208c405514d32,0xbc9750c5219843c7c65f,0x7b2a27fdac10d3f2bb68,0xca6da004dec7c68d260e),(0x9fc94cb9645f7727a8a3,0xa555919fa3c97aacaf17,0x3db42cd3c870b18bed87,0xaf5200095414d26ecdb5,0x741b488540ca7de3d15d,0x72edfabd93c41091b614,0xad20fc851d885d083258,0x28e2ea9d9dc699b3c5a1),(0x4a3d2e785156d21e5d5f,0x147587053fdcc07072db,0x252ffe486be25854d3b7,0xb2902d505243116220e5,0xdf98b2cfb90f3a979ef8,0x6ff9e9bb460cbb5aa71e,0xc5fc563913a23c94fe98,0xa4f76592c44980ccd891)),
((0x3201a94164f74157dd40,0xc9ca4c7c09e547263e9f,0xef1d100f891344ce5bc1,0xcf643b729ee42cbb425,0x29f57712c748287d3e2,0xb55a0f422ea30079cd3b,0xb644af1f77df9068488e,0xf610ea993f3c4c36da4d),(0x443c3de192e9e41b2c9d,0xdb0f94af82fb1bdb048f,0x4900ca2383bbf327c32b,0x9013f6d36e43107a9de6,0x9728e32c107101e00900,0x539dbec4d539fbeb9b6d,0xa2990ccc883aa4be4280,0x7207a7c5b20b4ef23c7c),(0x785391431db68fd2cb17,0xff1e71645c8d7151cc0a,0x94825c2c55cc7c7cf57d,0x661cff72574dfd5fb1af,0xbbec2092efed92d7b24f,0x4878633aeeee2132b070,0x683fd62331771237af49,0x61bfbb420d7b9a749c03),(0x11f7c79788d9e49e6844,0x73b1a97010370a1194db,0x4d16efceff704e819275,0xd7a47e21158ec8794b20,0xb5195709abad34e7fdb1,0xd022ed8a92c572d0466f,0x75bbcd201ef94abee715,0x1519be5da6fd2e558520),(0x1ab4f29c770a6aedf1eb,0xb95a47f83c1ad2e240e0,0x1ebc5f4db4e0968f6672,0xf5116dd542dc472778db,0x6d5669f44bdb9cc75173,0xc3d2fba505280095c016,0x832f85fd3976263924bd,0xaace3820d084f9ba6206),(0x57d30f0fa90abaf8efb7,0x29cdb531853c359ea9ca,0xf0f832a1afa5b41e1b08,0x6b5f9ff401826771d591,0xf915706e2c5cd517783b,0xa6613ccbf4967427350b,0x50c10d838accec7a4b33,0xe3c9b0836e1bf56c2310),(0x422d53822af91b31b219,0xe7b6e9c38a2b1a746a4c,0x82395396218609ca51e2,0x1de3acf28abc2e508447,0x179be550941fbbd5a2d,0xb630a2d9cab57e43bb2b,0x312db0711c7b1eeff4a,0x6f0696d7b698757f1972),(0xbc427c4ce9efa9e675fe,0x703d18c5d9bc7c3f33d6,0xc39cb8953adf79720ea6,0x41f9a1c598c01f79ac68,0x111089fe81a5dc78dc29,0xd9ad33fe7b0fc2784181,0x428576f50970afb739a3,0x4d302fd2815ceaef5561)),
((0xa5eb0c3b38bd4f60a6a2,0xd29ec16b89283f7be50f,0x59825b8c5cc6c09c31a9,0x734f621c634ca955ad8a,0x282c74d057565b01358f,0xbd422989684c6e04e430,0xc9a314c89c3f60973b0d,0x15f1fb9eab9225f690b4),(0xf1e69746b8cf2151c26d,0xc7a2fba6bb585a50f6b6,0x2b0ca1443ba53193ab0e,0x6ba5639f6cafa58bae0a,0xe5360cc36fbfe9f31fe4,0x8640d908f70a5851dd9,0x6435d0ae903268f13952,0x35eacd6c7b9c1c36c274),(0xefef12de5ea03a147f0e,0xb3632871ada10ceff9ac,0xcad205b255dea33c862b,0xb3b070d03fd5379e90fd,0xa27f6c6ae12a325bab9b,0xc46a77f834e61b46d2d6,0xbafd2d7382611068656e,0xfe6b3894b921465624cb),(0x4274278cfc8ff9400bd9,0x87341c51c924fb0301ff,0x9b22e6120a4fb228325b,0x3a683bfa227912e7b0dd,0x52f1cb5465bce8e64698,0xa5a19a48bf4c19adc88c,0xa4d46a2659ccbdb37ebe,0xd1a782c89d0181c3930b),(0xd309f7a392a287307327,0x98cd48c266ab0212be76,0xdf9780223c67e93946b7,0x2fc7ec57cebf3fb0acb3,0x7b88f672aae41bfecf47,0xbee0dc7cefb114215d1f,0xc817af3304fe4c6b2fe7,0xd6917870eb6b762baa17),(0x48d1ebdf7248390cf54c,0xa8d73cf5cf5683db4c2c,0xf53f7e10df9c1d8621cc,0x10de3ebb453e80896366,0xd1aa55f2ca96a6937d7e,0x4bc8454bd2e29b07fcef,0x8435ac2ffd4b152787dc,0xbac5a7eacb5ffd28c024),(0x6bbe9edffaaaacf4a9f3,0xe2cf88ceb35550688ee0,0xcc6c0ec91d726f4fbffe,0xac87a972708779ae69fa,0x358a9e5675235fb07aa5,0xbcf433484b1e8dfaaa0,0xfbf9a8e500a117c587fa,0x932659e6a2b6b788c19e),(0x8d85c579281ce7788f13,0x6515700b411c3410927e,0x85e85977df31e05c7c5d,0x3fa68a95cd75a44a6df2,0x59a06e4a27b789157c8d,0x32c15ab0f25b49cb84b8,0xebd06c9377a3c671a589,0xd72e24a123ca1c090fb0)),
((0xe4fb96a225cc6d796b65,0x699da09e10c282bbd97e,0x5afe115bdf0806f9bbd1,0xdb618d8e0f691b8b745f,0x21799c05968ccc15a7c,0xb6684cf565aae82c7d80,0x88b79a7c60ef38507b81,0x97c09d99f7d7bda8be3),(0x8fdf2ee5d9f53de77020,0x8b894482a2460095a3cb,0x2539c36f98b3bcc390e1,0xc3707ed06ea466bd2860,0x614f9f545660c73a3855,0xed53d2cc2b219f93b5fb,0xde68b1a77ca3454c8eea,0xeb835d8fbe4ee590e6df),(0x37fd6eff28c233101294,0xbaf00934d21030db8c37,0xfff725fe559808cc5c88,0xf66a733ae1b4f92011bb,0x3f0863df592867d96631,0x9723958741c8f801b4cf,0x1de85697ae4fd415668,0xcf10eb190c3d7b5fb4eb),(0x55fa81be450cfb7ef8a5,0xe28ebee3edb1cd54515d,0xf7b02438a78d379dcd5e,0x543b2886dc767fc6af4c,0x96b0c1a3d9200a896fa0,0x996718f70a73958e28c3,0xaed8fd4e070fc1fd1ae3,0xb356ce7174bc06f8e3f2),(0x9ec477c010685981d10f,0x7a0788b7ec2cb10e5af0,0xb7393c474d0161c841a8,0x6d78a3f55b19b6437306,0xc074ebf7187bfd9e6dc0,0x6839711adab9b12b243a,0x8bff1c16bd29277c6c5d,0xedae6f20323e85aae1cf),(0xb2ca97cf4022889f0cd0,0x67df44934874aa851cb5,0x6118f1b5425844e79551,0xb8497d549613b51c35b0,0x2fbba2fd5044d8a9d37c,0x992b2c360b7f40e9ee9,0xdd94b2a20b8acc717087,0x7023739ee54d09a114dd),(0xdd61cf3d39525aaac56b,0x8b0bbb1e24b27104c9d5,0x8ee00915f6be9649c920,0x27c9e4e39cd2311e813f,0x4f44ffd37f8696c7ae1c,0x9c0daf94a2bb2b014374,0xaf216ea11a87c9949ae8,0xb9ba320c1b33da5022ba),(0x207cda3154e159b77af3,0xf8a677b83be83c62c509,0x94d3a2b56739e9f46160,0xb57fe85561623e862b13,0xaa41756e097a37768406,0xbbbbc527c8d96716aad8,0x80ea52eed3ae278adb4d,0x70ddc8eccda931ae11d3)),
((0x1739c1620e9172ff9128,0x2bb78601d929a2f49bbc,0xc976226d16b5970f3cd7,0x5bcfe33f392105c2e7a4,0xc404f20bcdc6f3d4fb7c,0x9f5ce6a1f42c7f48b1f4,0x54e557d24da2beca8dd9,0xfbf4259984a31b3480d2),(0x7296c98dd1d5e01a6545,0xd8a55478890ee9067a2e,0x6226a1686e9a798b653b,0xd165f642541f4b3f6c95,0x3a92d2cd26e832bccfd2,0x120b8087b9a2690263dc,0x85e552df7a5e7b11f75e,0xc893c3f324cb448f1ff3),(0x64a34922052d6e956be9,0xefcb3b0f663b2595dad8,0xe9ceb9602cc53dcacdd2,0x4df97bf7103c89b9bc83,0xdc8ccc98a6b8ed18741a,0xcb31cd98a8fc0d444573,0x1f21fa083af5c416a000,0x15ea05f6bc9ac7fa9997),(0xb5618d2b75bfc49daf5,0xaa64bae10d54ee95aa66,0xfa141b2c7bd0e13392aa,0x6a58119595b0a13155b0,0x938c27709557a79d0efc,0xbdf7963d85103d619054,0x2f67701560c3a8a55701,0x3e96a71bd9f9636e31e8),(0xc64770e176ee3656d0ff,0xe580a47e60ee221e09d7,0x5c51195b2b41bc3fff04,0xd9ee36bd1b9664da9c5e,0x82bbaa0b06306e6419b8,0xfd635e5a21000f0228b0,0xfc7f33a3cd8165d2959c,0x7bc037d3e8e9b8d01b71),(0xf57ee6e00f41cc8ae04b,0xb5cba8d2b75a15f00a87,0xb98ff113fb2710290bd6,0x39ac5a9375e9deb78378,0x9611e8afc80e4880f464,0xe3272adb22a31a4807ff,0x377bb62936323a978657,0x4d19593d05ce8448bee1),(0xe5cedfb94cfa5a462848,0xb8e2908adf7198e6b4b0,0x3e23378e5bd8351958d6,0xe0b9226690f8673b1b80,0x724e17a520553c4eebff,0xbea184fade46c5274ee9,0x5822603fab47324974af,0xd3e4cd8c8d417d0ffb79),(0x2917b8d175527d16e1f2,0x244ed72b8ae8984d1ac1,0xaacef393372161aec850,0xaf3ff0bf0962e3fcaf1c,0x2286b43462a1e2652547,0xd5edb741bb3143528ada,0x7fba7a6ffd7a8d83856a,0xee9a028122f283fc3604)),
((0xd2400d43883839e4c811,0x5b93ce08513ebabfbdd8,0xa469f749cc1c92fcc2a4,0xa9aaf9dcf42808b2398c,0xe14f04c195501c77c86b,0xe27494e2edd25e1e2396,0x85b080eb619b35313dc7,0xd8b290c587a3518f5f54),(0x49c8e59f3a74dce76543,0xa86aae3caf7e19d7ce77,0x10369bbf59a38328d8be,0xd795908544ae80f55ffb,0x88281ec6d96588e808f9,0x98a16685ed5a6e10cd11,0x16a38d97b92dc8af0b7d,0x785a0e79936cb3c8d86),(0xfbce485325ab7b2bedb2,0x43d5f8758bd25388c8a3,0xcb672cd41bd767dfc928,0xe0756c3e63bf4032970c,0xf7543018a4245436e8ee,0x8b241376f2ce27f4c064,0xd842fac9795660a8ed5d,0xd3a34b9d5f659057f768),(0x5b587f7f1fe4f6d95fd0,0x874248774cafce501543,0xe3863b24d3aad08b2cf,0x44a05f879c286b469d14,0x767a421ace531343bbf7,0x561b3b05963999aa2560,0x855d0e13395096897e1f,0x5a8b954ebbaafca55829),(0x53e4967cf0e1309cfd3,0xb0cd11250c4bd534e064,0x6a8efabe3099d39df6b7,0x743657879c293fc8152c,0x2e0476815d2b2708e4ac,0x4192e36beda911e12293,0xdfcad7fa374d387dd11f,0x9155d5d31a4eabe6902d),(0x40547ad92dab073ea94d,0x951c6cffefde05556db6,0xb200a55f27499ee3853f,0x4c0dc6b200b5c70bad01,0xc330c22a6bee024d66cd,0x4ce3f4565dbf3e11b94a,0xa9987300f4622847e133,0xb3c5c796c84e3f5915cd),(0xb036eda7c22375788eaa,0xfdfd763bf5aa97a43003,0xec09099fb7d049a0b457,0xf9db44cae6a71c5fbe68,0xf9202434776ca2e949ac,0x5d64f92e434224654d9a,0x8424cb559e856f95d2c0,0x475af939e6f5097efc50),(0x9b72d46132e2fa7154d4,0x42f931c154ad609a1884,0x12596e9ca2c332a33e15,0xb12fb6b917c19407f555,0xf18cc9e7a210b6b43809,0x10aff2a12a503f4446a1,0x1358477f98da2dfca936,0x54e2750072b5476f0c75)),
((0x55c6af9d33a4372e093b,0xf0b9c0e7f764b03f5eff,0x9a8a590b03adebb9e16b,0x3f9861fecbc514aae331,0x3c2bd71df6a9ceb5b753,0xb5d7157b1cf42528f80b,0x35a496e334ab6d296325,0x1792c7bf00ec2f504255),(0x91329f3c3ea05379ba51,0xf145923114ef3753063b,0x65055ddfa303aeef9c0c,0x54c25908885b898be81a,0x32bb6d234cadd5d545b7,0xc2e53bc90abe2dafa22d,0xf61efcf1808e181ac6bf,0x5784915351ddfc12ad04),(0x2f8f12bcb21fb416c450,0x748b8a60ddd8de59a19b,0xe13fbb31d59aea7cc219,0xae9f14e78e9562edaa9a,0xbd9efc8d18f5d4f1de04,0x819156c825c36c0ed697,0xcec9b7d0f2e1edbb0114,0xbab818f5b499b57050b),(0xb3166971acb222b58d8e,0x6d0464891ccc29648ef6,0x72ab60d5c8fba2d397d3,0xc7eff1c00c53c4bff1bf,0x250a63d2bb0477aabc6,0xa12f5e79dd8cda0b0828,0xe5e4d0f1ce30b3991d04,0xb99a6909e0a30e78b437),(0xd7d1cf71542de07bc794,0x2dd6c2406144ef5d1539,0x24605ad1efcd82360b63,0x17dcf74054c39116f5f5,0x10c94402315c8a806039,0x5cb892837d5e110980bc,0x330d727bc8d0df005441,0xc61f1a06a4a582a8d153),(0xde8bfe47c0847e52cc94,0xa404063c4e46720dbcdc,0x778b3e9c4a53f843ba51,0x6d240ec98b020084627b,0x3eb6e703e7d9f94b7307,0x742e8320ab9b8e24aea5,0x94de64d3ac8c8e8778a3,0xee16671af46b10ee537a),(0xad082f90b89b5c8aa0ea,0x44e0c2dd0b3e2461800e,0x537ea1edf8b225f43eb1,0x1193a95ebf72e957b1e8,0xf15ec9966fe5ea53887,0x449e08cddf0cd51d053c,0x2a46f148f20bdcb2436b,0x5ff1657d67b10877ab40),(0x8b89f03ecc33ec9dc0d6,0x264ee2eb16c47c2ae95,0xeedc696988d9234dac56,0x78334770f7e59c1fef5f,0x9f03c184fd3821cf1fd,0x5425756ac1e59b930ad3,0x220c488524582dbe6fe0,0xa187c278d3e6e21bc63e)),
((0xfe5403e4a7886e033c3e,0x9e59c3d787d9e4bd4500,0x4a5e047708ba226020b5,0xe17d15641b588f72e350,0xebac70283e43ba38ba3b,0x709dc493622eaad3e2b7,0x189633dbc72abfb7dbc6,0x843bf8fb1ac002c5b76b),(0xd48f0cc2a303a08bead4,0x3b52f8bde108f8249335,0xad7de65bb6a85b700b6e,0x9a3c2e7c5352932a9fc6,0x212a8632a40d86f5d6cb,0xbb29b06ecca82794335e,0x32bfb487f2acae76e384,0x18a0aee398a3af61f551),(0x2b9e09d301bc6f5147d6,0x309734a3f9743bec3e32,0x102ebc473f6c08493662,0x3e97b1fef1b5889d1445,0xb3802687d01dcb08d8a1,0x31e9a1043edb215a2c05,0xa0df02b0cd23a635ccaa,0xf23aea63d6144504ffa7),(0x55aacd2bca0cd11a4045,0x1f6597ceea440cfc6e85,0x96ddfd34664da945d0a3,0xffdb71c49bd33eb24a80,0xf64cab9be06be2b84cf,0x6c135eb68f3fcb8a5cd0,0x2e2df6d8286c6b7d3269,0xb0aec768e0cbf7fa42f5),(0xffca81eb3ea0d1dbebd1,0x4ede3e58bf3f209d07e0,0x6295a84d14e30ad035cf,0xab85a380f3a0586ebf4d,0x8363aff80ec5fd56d823,0xd75f3d590e0b1d964ccb,0x8dc9fffef8de970ede68,0x74c41c0b3865a878381c),(0x7377b8991c6cd9fcc9da,0xd9e524564e1a7007dee7,0xf545e142e4575d064a9e,0xd9e6a047fc725e8bc2d,0x713fbd897260aaab5360,0x5146012fad0e4597fdcd,0xa8319eedfe1d937f31a1,0x22ac1f6c0a004a45e331),(0xba53f5c55755806abb6d,0x909eed214c982b1459b7,0x5515fb103b9e83f1211e,0x7a3626bf8b4d6cf39cc0,0x7ce86054ba77db19d668,0x47cff5c9e31571e21ec9,0x915c7af711f5102aa7a2,0x2443cb95d9b46d8d5f3),(0xc3eb54ec36df5a2d1df7,0x73ffab6e2abd4716fc5,0xa455374f85074b4a23e4,0xbcb8d382890b8778c0f5,0xe9bf7352849fe3d9c2de,0x5228922f6a4631c32601,0x2fb8cc3bfa20dff95efc,0x12055553c6b4c1e127c1)))

def page13 : WordPage :=
(((0x8c4e5340e87c5c1fadb9,0x9f607b3f032a2e36689b,0x4e8dd9494f359192af2d,0x936f1bc99ba2fcca9ae6,0x3bdf4a887307ddd16f1a,0x81d82082f7cff991616b,0x6e849ede60ff8404daa9,0x6b1adb6fcfe51131e3e0),(0x8ca7e3408f6636eb4d13,0xa058ace4e6ed5c07bcfe,0x4acff472bf197f6c06a1,0xcc1f593b7e8fddd81a2,0x4db679664f7fdd601e88,0x475ed70cd08c9326b83,0x1f968f9a912d16dadba8,0x5bad30afbb84be7f9ef9),(0x38d41d09909a56ef998e,0x9f64b9874fe3474b862b,0x3011c65b39e2763add3,0x20f27207726dabf011ba,0x46c051103814b7d471d0,0x2d09dd2215c9f2c3d099,0x79809e3197db9ddc49f0,0x768876ae3235b35df189),(0xf27b141d29ff716b5dd6,0x9814c5c48d9c82c95efa,0x1356870d550d01ef7d35,0x476fa06f7642018844c8,0x6a7ed05019bdda6e92c7,0xd74de8fe79382db5f089,0x3c1ce2a5ecac70cb18a4,0xd60eafcbd1b0285130c6),(0x36b2b9b23592472bf3a6,0x45644d28fc1843b4edc4,0xdd576a80501b899bfc8a,0x6406ebe0cdc79f998e52,0x5326deee61cc1902ee42,0x5aaa0afa49c0ca701693,0xf71baded1638343f042a,0xd1fd56d0b117dbf7bc05),(0x8547950aba3aaa434ec8,0xb185ac409f320e7f5d8c,0xb5af875f79692a8979ea,0x36ee2763782d6cc52446,0xb4fd2e606747104d76d0,0x466847b35e0231d6f888,0xb46192800058d13f3169,0xda022e965f6386625616),(0xb9e7eb357d3108839750,0x441cc7654f8531c5f119,0x99b5a5f46d79570e2251,0x47ac13bc8bf7065ad67,0xd07fdf9a6be744e51110,0xa9b57d06a6be55afcede,0x6ff516e6b31ad7d6befe,0x27ab077e16609da20387),(0x215360ded7e6cb101808,0x1ed663516b9c63f44a59,0xa93571c0e2f76032b68,0xffde66501459859a5e4c,0x67ad94ededb1501dbf95,0x40355f47aca52577db14,0xc2ee0120479dd4dcb5fe,0xc38780a219806ae82c98)),
((0xb2ff9e12e8733620a910,0x95d55dd86dcd386e7785,0x5007e81f95d1f55e43f5,0xa7fb1b5bb45286700f9,0xf03846377e89a73894a7,0xb17e36512fad58885f37,0xbe18567549eecc2da07,0x2d81afd4938c5c84f87f),(0x33c7b3049f37345e1a5f,0x8fde77b44acdf02eb077,0x2cc56551eaf47a265510,0x39e963024b9616647f5e,0xc21f587de3b3dbc37b43,0xc3baae1a6521abe1f96a,0xd27335d1a40f823463d,0xb6da85892a3a0d66232f),(0xae9075aeaf55bcef85f3,0x1b629c2d91a7bc1bfe91,0x2d6393ce38d00a47efe9,0x62b89d55d4f86006e3ad,0x3cc1788a987b26e9a4d9,0xa39107bb2b47ac17d623,0xaf935cb9a646b649c619,0xc37b2ecb12621f429d30),(0xb721ab92a5eda94dc46b,0xea49341b9cd22eb4aa6d,0x24f3573eb7b5c4b89a5e,0xb11437ceeb89d6dedaf3,0x9a5a9ebb0decf621eb09,0x860b7db5500dbf234452,0x33c48cac27236f9ed6f4,0x92f94f90da6167f54f3a),(0x87e53c3b47a96b7d082a,0xb86f40774ef41dc250c1,0x4aa9f74cf2832f24c7ae,0x704f56e75580f8f6c512,0xae703b363dd237c5bdc1,0xec41b8ec485786b5154a,0xde175b24bea00408471d,0x9d0d97798b2f176c350c),(0x1c92566c1395a37fbde4,0x76cf19b812499a36ab48,0x4e11f4a0c8b68ea6748,0xe4f0230aa7012ace5959,0x959100afb50711462436,0xd34a6f8f15eaa14f5d8c,0xe5d1d47ec9645e05da20,0xc52576b7db8ebe43465b),(0x65a971eb28f4a2d16b3,0x56daa616991f11f2454b,0x3e36a1244d595a802e57,0x8c871c9551bc1ba5dfdb,0xd0167d4dae1c6c858ad8,0xabca1d96767841df965b,0x139c08626d26507adee7,0xd05e799bcfc91a59ce0a),(0xf6008039cc448f2ce7f2,0xaad2bf3091ccfafa488c,0x163dcbc6a5ff4aec1aae,0x5a24269b6e0cd5026574,0xe272adb3bb2899266b7e,0x51c9a6fd134313b82be6,0xc6ef4b60b23eb0642d,0xcdee2719600b39722d2e)),
((0xf0201e38bd810b6a8051,0xf04830b40de4826a125b,0x33786ba2709be6140656,0x802b387a73552698d083,0x70b49b7b7703d11abdc6,0x3b6853481ff12857817b,0x43bf7572c18335aae360,0x1b01318e28a741b21904),(0xbe3343dc08e4f0be6ae5,0xbeaa517058a2d70f1308,0x490403bee549674d1f87,0x4210976863bd8f662277,0x8bcc0fd5122bb40c608,0xcce9ee72314f2acb7d82,0x65db008a1aebb87574e5,0x21967c6d0fa44dd5d785),(0xe19c01242c835a0e87c3,0x5d3d781fa86b47aeddd5,0xef6e0a242d87658761bc,0x7cdb595818c2566b0f31,0xf5933845d5c961baa944,0xc84d948a8ae4c3d9304b,0xa059575784178ae3ce86,0x26e099d16d888901272),(0xdbb053216dd9095ca21a,0x2d3adef96f966a79e853,0xa432bb1bdc3d4fd2dc4f,0x512b4f02d4d5b1611061,0xde4c302f90a96235cdca,0x99bc8af3333604b73ae8,0xf8723db5d7da9d0575e9,0xb2174e575c191f04e3ce),(0xa5d6cb518ec28d54fac0,0x8d3542a64b3a2f27d7c7,0xd977b074d9d48f705ade,0xbe2b1d521574811f7663,0xa57a98f1f523b4467e9b,0xde93e16306a07b4effd6,0x102a6742ffb739deb40e,0x9ad4b6efd846333189ae),(0x938becf119881dbc0b05,0x229c8321a0d4f1146fac,0xd47edfb326999aa61f80,0x48f3ec2137360fdf0e6c,0xab86f7083a6eeb83521e,0x6d339aaf93803175d17f,0x750e82fc333ec3e4ded2,0x59a96af49fe9dbbd70ab),(0x3df800435dd85a39039d,0x5b3bc20ba665aa3e9db7,0xdb85d552a9667407e556,0xc8a9df30e395d2a4df5b,0xdecae6177e2618930954,0xc9c13f5a1afe996b4410,0x6eb92de17bf8ea1148e1,0x68ffba13508b9380b7e5),(0x9f512cbc27a468f23179,0xe0d5f8b075a7c336a37d,0xc211d2f557e7dbdc3c37,0x2e7cf880529f0e3af1a9,0x37a3bce0f4d4390520c8,0x6b4db629c77a33137d69,0x43d7eedbd5e2fdd54691,0x598a2b58cdef761bc20f)),
((0x570ddc78dd9da999ef74,0xe570a5a9ab50283e9b43,0xd8532c156482d57992c6,0x90cc7949e0b318f25137,0xffc1119137236894b8e2,0x88c0a3f5edc42e7c9ad1,0xd8e05b53c1c7bef02241,0xd4ffe492fad801332f35),(0xf0d3609e76e4da7247f6,0xcc1ac6b4ed6b2078e2ff,0x796f04a86d17ba42827e,0x4953102366b956679c9f,0x7e96c1c86ea8c30f4bef,0xd2b859e2fc72db6db915,0x759a1c4c3e949a163679,0xb5a87356ecd3b7245ffb),(0xa052174542585377dea5,0xa37e1245d92abf45f2ad,0x63d7d407634f4dabef49,0xdc0d01bc6f451a108e61,0x80880c5754b7789ecfd5,0x1233b6f7ad820560844b,0xef6fed64545880e576c3,0xdf32567125d8fea6083),(0x3766c81d6ce5bbe22ebc,0x4109af265305132dfacc,0x951f8e09b5580a34c4bb,0x32e9ae6f4a0051fca761,0x873e6cf13584243b77a9,0xa0f326702079d878382d,0x4e1b316ac6985f2d03b8,0x8696b64d047a9bd81133),(0xaee56974127a212d6a04,0x48c843402ebe1fbd3ddd,0x337fdbe11801841962b2,0xe8b10a3dd745fa042374,0xbb7249f955da27c669c,0xce74e1ab06f00cf987e7,0x234c6c0ddd65de7b8fcb,0xe4cad3eb034b9919d9e7),(0x4b6f38c54a055c3557d7,0x162a5daa169e35449dc4,0x5b67c08c2b2bc15e618b,0xf93220ab5e79a418ba2a,0xf16e935597737c04cf66,0xcae566c274b02e3a9ec1,0x137bfb68ce843ffa2d67,0x5c5fda08432bb4c463f4),(0xf5a96a84fdf0ebce9ac6,0x6a0158a294dc3e5140c0,0xe3ee00c812098ce61c01,0xc553ef5e2215a582d1c9,0xb6ce3fb77a3b55a45bf6,0xa07edb3b83474a612e06,0xa28fb198851621db364,0x31eb3ca0b5d72757442d),(0x5d4b57a9a1dc8169f51e,0xa3322142ae5969f1cee3,0xb7bc478f8d335ac68223,0x30b6788d627b8dfde458,0xaa1888f7de2b9b150a0d,0x5a8546a0c4d6b5625cdb,0x391cb25e8871b7d9cbb6,0x7b75ce1ea5f7cf8c0937)),
((0xc89eda927edc88b83775,0xccc10b028017b28065e1,0x75c664584dfb00f03e42,0xda895bd2753a79cb6b64,0xfd7b069cbc2e80db40c5,0xe5d9b8a742a9179d607e,0x50b08df52735eff4602e,0xfc15259262d6ebdde1a7),(0x1a02561ecfe111bfdb89,0xba05e2d50574f2173df3,0x17b8a288741710ed1389,0x957ffa0f6a03fecb3be0,0x198483149abc0fd5de88,0xe35081f8d67307b3df46,0xcbbdab66c1b9f4010f52,0x92008e3abf0f43abb709),(0x9bcc7ec865d41fac363e,0x35b7a910afec57d97d87,0xd4576e79a33839c90466,0x50fc14fa966fcea3e8f3,0xd5e869a4dcda80757b03,0xd5ba64716db4fc4c21f2,0x659ae28e1ffe8660b041,0x6d3e0123c9fd885d6f08),(0x3bea40b0dccdce3fba2e,0x280a353d49809df11880,0xf4113d509ea97df1d783,0xf5af273f7d910a62bca,0xd390696b80f0bc9bfc15,0xe8f452e0f4034e837160,0x71f1cb3d710e191fa0e1,0x5fa4807752732850f7a4),(0x4996be99088fc272a1c4,0xb06980f73f3379fa6499,0x5d725ff2f6aca5d201a9,0xf18702babd9b3a95669a,0x9e8ca746e00fbfb13270,0x33e894a649658bef7eb2,0xef1cb9be7f0d1d9a2850,0x17cc8bdeeb3627d8a027),(0x673b056f53d78ceccc3,0xc8b8ce7e47841b901ef4,0x415f2861eb01733c172b,0x8264a8a492db37d98c00,0x15431532da2fe19359ea,0x45c94685d5b45437d636,0x4b4cd76154e174c43eb4,0x3468da95ed10037a5f26),(0x26fda640bffea9f0a954,0xb518d7d296fc6d60ba7d,0x8e0fd150e9aa98665aad,0x5b2116e530cef1df77cf,0xd889461255dce189ca11,0x737750912b30d2d11a28,0x56e1961e44abd04a1bbb,0xea22efd5fed834021c3f),(0x3b56e43eeca7def0a1b7,0x47ab8f88d0ae876bb160,0x3aebefd00cfa159bde00,0x443a8abb5775a63279cb,0x687eb871d96ed6651e61,0x65abc02c7bc94fd29736,0xbd215dcd7980d05a74aa,0xcf878c216ed74b1acc59)),
((0x1de09d4071468e77d972,0x7fd85837852c283b6b3,0x5917f9fb5f4815ffe1fc,0x9713b22970abc224bf39,0x3d20a23fe9b8d8abc6da,0xa17eaabb704061970035,0x913a3dceb685d7b3d201,0x5072f09173627ff3855f),(0x613fa3ceab2045238177,0x9b3bf9bc101e2062dbb7,0xfc0b5860d1a0c2543c6c,0xd2ac2c6d7c8a9eafa76c,0x1affe232b18ac43d266,0x20038faec06da1f94fbe,0x21871d82a6d2241c8782,0xad8c867f61f0b8efe5f9),(0x9043dd03db333314028,0x483151804353fb9216bc,0x5b7cbf3168935e2d1161,0x10456829354ab287ab66,0xd573daf89dec552a55bb,0x448f0b2d1a02a780531b,0xd95a694c76851fd740db,0xbbd60c1bf433f7fbaa),(0xcb81f319f132ee3638c4,0x2d4ff0e708be0b09425f,0x52a17285151a818d16b,0x415c1f2fae147b8c3f1f,0xd31be678e9c4eded7630,0x318fb3a572ddc0f9dc2b,0x346a87b81549933a3107,0x51a4e958db79ec115244),(0xf5f6c211cb2284816e32,0xbdc29e61fd02ff0a2da3,0x87ac62667b187d57ed1d,0x988849881e21ac7c9a9d,0xe3f48aceab8a0656c6c8,0x85b4a9f82473892fb3f5,0xafce2a65ec9ac59ddd5d,0x579618c9ab3c9c491225),(0x23696dca547959be3b8b,0x319e1ec89e088ec14b82,0x6abd58350c6b2f6eddba,0x95ef723e313aefedfc74,0x5c178b57e78bbb29298c,0x8854a21fd9a95b992394,0xd18d8861423b070e7b0c,0x2095da2f562219698cdd),(0xa7cc23a29ae1926ccb17,0x1f255af47c9ffd0e8510,0x8ffdcf77828cb281db86,0xd358d4d3a77fd392ab9b,0x5ecee945e74139868f58,0xbccc45b534019e18ae84,0x319ac7d4c265c0bd7fe7,0xa57d4e86612d75db8877),(0xc5fde7057fba503c1f5b,0x79068186f5362486fb4e,0x47664d3d78630e66344a,0x60051d2fd754a49cdf56,0xc5b1a3caf067b2b5ac3,0x42a0e904e98dce393c2d,0x552640c4adcc5bf5e711,0x63400cdd4653f357d933)),
((0xe4722fc1cb8959993cf4,0x12cfb27ce7aa96a39497,0x1aedbe6389a779c7a645,0xf4290c6c0371060207fe,0x7515a28859210cf01875,0x3e0af3a90084df9c3517,0x530c489753a7f833fe8e,0xa739993a7e217323ebc1),(0xe4a83e835e79f10a55c7,0x54b29a1bf1b78f2abe22,0x4b24c207fd6d3e4af82b,0x2358045d521f5bbab532,0xf14539e7c21b8df9dd23,0x2df621334606c2cfda17,0x439e88d75e7e74fc48e,0x5eebae62ebad8acb03e2),(0xfdc6e5054468ecac2d44,0x4a9a89418a596c81bf6b,0x95f180f35de38575735a,0xa75f205e45e3039b8160,0x6688ff644de029c3a524,0x100ed2ba509cef69b8a,0x81e7fabe8fb2f524eb69,0x36229e909de7787289b2),(0x30cd22efc795a1921dc5,0x60e554ba4044df9febc2,0x9d0411798d85693f1d41,0x82cc184563675470f5a1,0xc008ac209c6d3d348895,0xbfab9c480a0d4c0259a9,0x75305ba33fb4582ce5c5,0x80b8c0c2fe9caf594fc6),(0x41c4f780ccc962dac76b,0xc6372c232f00e965fdf8,0xcbab033a0ed62607f34a,0x372f9c4b84c2548cf62d,0xaf991e6f029f8957399b,0x9d11b86ffb6be71c52cf,0x598d816d4fc83622ca67,0xffc4d0400cf50dea4893),(0x41488925e39905f667c8,0x9862fff2ac87e4f39dd0,0x4c97e4c84a9f68e73079,0xabbf0ed0da2ed098d8e3,0x7b6b9d02c3e8263cd37a,0x24ea58d49ab084ff8dc5,0x3545b4322ea3a791d4c9,0xdb4a65f2129b1c28ce2b),(0x4af07f5070258b476eb5,0xe8cc66044eb8428c36d2,0x947120a685fec54322cf,0x1778e96243b6d37b37d5,0x83407ffaa3be47c1b252,0xa32940cc6085c4b0bd49,0xa3b666a009fa1a997ebb,0x47be44e3c0009ca02897),(0xad3e4c05a5cb2344913d,0xfdb543e7fee40ed4d739,0xd1beed59235df6d032b1,0xe633484a5fbee6a8407f,0x7935e4282561dc16ab00,0xd7d14b9da89ae7355b9e,0xcc0609fc4e8677c78107,0x1ebd658443d133d44236)),
((0x16d0c15b0226cc95cf00,0x9386e1f1c4e7b041441d,0x3273ba405ffd9c04b69b,0xaed6d1d0934a2536eb0d,0x9ac7db1c85430971a251,0x4e56ed6633a38f857cd4,0xf89880c2a4e92268000e,0x26bfe0394539ca610a2e),(0x557a17b188063cd3ce54,0x7de7d8aea035f890593f,0xa32b5cb185519bd41b0,0xd5e4f4322c9c249f1299,0x64482c72d9bab10ac585,0xe4a4067246034b71a019,0xa99ffe9532f514d8ce58,0x42f1b21f0cb7f4cf0196),(0x3c8e9fde3eb423094187,0xb0a44da621648d53945d,0x214f69f982b73306f6ec,0xb1786971f00b3286c306,0x82084b62ff408d1a30a9,0x8c1791be65f65caeed19,0x3f789c38210a5f453bb1,0x64abe614dbedb913be5b),(0x2a15e760160d41b63e9c,0x67856967175ca49eaade,0x26bd24ce2d7349c12b9d,0xe2950b907caf74b13b49,0x4c1a32efd689add4f4da,0x6bfbf04e347317c1fe3f,0x60b0d483444e704dbd90,0x1899e005e4b6bbd29919),(0x8f89fa6226d630ded65a,0xc37d54234f659d42a40a,0x7d4ea1d0d0a5069b7e23,0x9fddac7904162dc1874d,0x207ef5bfee8dedf81c69,0x886298567855a37596ea,0xa01a60bd76b708fd574,0x4e48f5a4827d85f9d5b7),(0xe33df629abfd3333ae20,0x9ef9b41ea7bdaaa2fd22,0x8adc6ee3b6ef8cd6aedc,0x43c53ab78770512114b7,0x66041a34cd6fcf4f6dda,0xc12ea0fb3d7ab0de3dc8,0xc139480be54ed87e669a,0xcfa01ef328b6b1956578),(0x2dbac439161ee6df50e1,0x478c6f636b61c2900071,0x64939bbaaef2a2061dd5,0x416401fcf9a53060c668,0x4b9632a81680a3009179,0x4ac98828cea528e82c36,0xad6006e8284fdd685139,0xcd49bc23c9b9762d1e23),(0xbcb320989fed4ec4e469,0x758207dcd1d35281ee32,0x8b7b5dfe688414e9e157,0x1a9079ef3573ba57b0ee,0x4ab8ad2e0222b33577b7,0xa226078cf26c96baeadf,0x9a45bf8d4d06800928ee,0x630ecd7e60c34b2f91f0)))

def page14 : WordPage :=
(((0x2ec792a7d8f749125139,0x20eabdf272c38878ffc3,0x1b3336fbebf2c1b0b954,0x9a8c9517fae098c46e9f,0xd061a81fbc536fa38f02,0xfa38861b8b6847f27cf,0x1dfd28b518b417cbc515,0xfaf75f24cbb623819e2),(0xf44b14bd4fdd1cabffb3,0x4c6031cd79f87cb8726e,0x9a20d253cdd8035afb9,0x27cf52fe1652e7ad6832,0xdf9dff82f60d684d8f0f,0x4b2a340d3d019261cc87,0xf04bb4ef4ac81a637ad4,0x848f98a7f2e022f9e5ed),(0xbfe76c725aae4c82b03c,0x1cdc21a35f0d48eb78a5,0xbe62df77e7f449ca4ba5,0xb68483c5385c62cfa08d,0xe6e07a6f26ed498caded,0x8176990bd5eab467d9c8,0x43ac9232eadf63a99ea8,0x340a4db0f3a99c98bbe9),(0x4135797bbf5202ab81ec,0x36c06ab69f8b45f46e40,0x5aac9f72f305b6487a61,0x92cb65c0bd69621e4c57,0xe728e638e22faec9784b,0x21447de30f04fef2e5c4,0x79f0414c299fc9d43661,0xdf7d9d14b0bf9e63a749),(0x9a278a49fc11df0ea3d2,0xc96777775178a0234684,0x69830e35b6670c007dcd,0x4bd32d79c84cdafb1d7f,0x155b6a9c1d8bfef2bf,0x9410a5d15974bebcd0a3,0xfec9743a882c1a05034e,0x6b358d34c0c1107ae15),(0x7562ce23f71c799284c4,0x5d65119754934d413246,0x83f705aecd6de96d0114,0xc3c41351c37af4b8b6ec,0x208c0b896f44a3b0d948,0x5081506885e131ba4a3b,0x9839a5b8ed29c99f55b,0xc4c410b4154215c955a1),(0x20035ca1740868b7a4f4,0x45fa663f6fa79e84b480,0x5dffdb6274cc160791cc,0x19adb52a31deb96bdbfe,0x3b233b93aa55c49176dc,0xd20541c8da3db114ef51,0xa8eb2aa2d0b4c02cd90f,0x4ad158a20523041d4cb0),(0x9bcf90fcfc92c21a4a21,0xf1b33eacb56e9d499eac,0xb0c2c84da48c9bd6001a,0x6503d31f15eaa6bdd28b,0x65d9e27d17b43edb50bf,0xcc980fbb92b35f6f32,0x1386fafcc3a272ed63,0xb1094dfc9c184407a38e)),
((0xd13ce695fd8fecd219c2,0xe6f669e11e4ccac216e9,0xe409c92f1a360a8d5333,0x2dd8b861dfee585ab711,0x800b93ccda003d2be8e0,0xa7bf6f9a319f6f94b2f2,0xc2196a8a0a0ff910b26f,0x207e110ec18c8aac178c),(0x59307417a2ffe4ae3fa3,0x7d12e32128444b493d90,0x18a47e3cef062e8befa,0x4b3b28f17c91514eb6ec,0x111c47f9cc987ac4fd78,0x741ee920ec038e3a89f1,0x17afc204a14ba82ea943,0x1401f18d0ceace55ffbe),(0xd52e01a8718617fcfc6c,0x26c5cec137011d5e7310,0x9bebfb3de4038e96ab33,0xbcf951ab084f39efeb21,0x902c9238cb208acd6a24,0xf256c5ae5e6884c0db96,0xec378151432384f21020,0x722eaa70d1484336bae2),(0x8e8db01a9a92be493657,0x669c8bf90eb1e34b3bf2,0xee73570b690102aeddba,0x8cfd8e1f701bdb990d2c,0x743aec483e233cc0f6b5,0xde768d4ae3ff98a415ea,0x98b5cbec817ecf945916,0x4a371fbd217fc6d76c97),(0x3aa216fe942c4a271326,0xe374516e7ffd3c642549,0x8708bd68f13001852177,0xf98e0e46bd8d0e6d52fb,0x12f24311e8512f9b529f,0x7e09f51c6c1021b1649e,0xabdc61c3a5ebc62d32f2,0xe15254e718155634ad14),(0x8b775ad30bc5b305dc4b,0xb8beb6016b51081d5c55,0x9091d94781dfffd8718a,0x534a3042f23a83471c28,0xbb14fa28b5071dc2c888,0x9c9ece0094e6018ca4b1,0x8d1cc1d0bf99d415848d,0xd951ca746a52e7d9ea1c),(0x94f00cea63d0a77f911,0xb5c23568be01f6ea32e7,0x2ab4d614a83849ede1cb,0xfbc709b3d0e00eb9b3c8,0xbfbea1a9e8e3147e7de1,0x1a3da8693d78d82dec92,0x6c2f0474e6675476fa5d,0xdb269b2691f334d157c8),(0x104613c114e053b6081f,0xe9f384b6fa89888dc26c,0xa0132100bdef8df59e75,0xc11927cb2b68f6c29109,0x26d9338d2c03b6683c82,0xdb6742b93009eb4ba5f6,0x48eae3358a2d7c390d4a,0x67d2167a1cde91129d73)),
((0x7c70be48a5db605ab427,0xfaf46e58e0140f98a5be,0xb79c78e574d4a6eb6d80,0xe90206850101fc8d3a98,0xbed308458a8f47187c70,0xaf424555e8cc0ea2ff9e,0xf522b175a576611aec38,0xfdc04ef6bc90e9befefb),(0x7572a942d6046c2232cd,0x500095a15881e08d9157,0x5813158aad8be561989c,0x73580e30d927d5787dda,0x69e189f7a2576fb0c454,0xd1899d955311d742fd18,0x96abaa34a3e8761b794a,0x29412299fd6a4cfd0bc2),(0x726610e1c1f7676f75c5,0xd1a8131cf6c663b73474,0xc80e0974996bb51d9168,0x2d28212ea08f821368c,0xc000cd0d3beecdd055ad,0xeada332b41b619475bb,0xd0954394e45c8b2d7225,0x4fb12a5e36368a25d6aa),(0x13a56cfb44d3ab9cc578,0x6fbbcfe369ad7fc7ea9,0xc994ef00c6c5b77809fe,0x80e44ec64a20848f3a43,0x34a7859542dd78029718,0xd60d4e3e78e2c22886df,0x47fddc94c9de19caf7f0,0x2f84f7d3acda771e2b28),(0x766108eac4b49c0d7b42,0xb0c0e8def4fb21fc9ad1,0x84148ce54b452447c874,0xbcbcb51d6b194b78a900,0x3ef8049a7b9353543293,0x6eb7e4756fcd0d06f366,0x1dfbafa74b08452bba54,0xd65d15ce7110dd5f5143),(0x6df134fa91368c56183d,0x9b5be90185df4b45130f,0xec8dabed17a7b3706011,0xbee767dcd6d1bcf96198,0x462966a5e0db0ca671c,0x16031698f084e6ee1e66,0xb7076d8691da047a3eab,0xb451a01bea678f4d823b),(0x72f1411df5190c2ddc9,0x6c059fbcabf2003ccce3,0x6579f56b5352ce3c92a9,0x442853eb729a16c9010e,0x792d1db4a2cef0e9879e,0x7191cb5c462c21664402,0x5f36925d3124f5d5c1de,0xe40f3c1541e5cff77b),(0xe70b41f4faffae95bb8f,0xaa2ef35ec3d286740a10,0xb1892300d5572ada33cf,0xa92639bc7bf90146325f,0x26f79b2c2700be1134db,0x5e26ec7da1689896fd0a,0xddcb8fb39560ea55b4ae,0x4e0813b9a9a5f2cccee0)),
((0xb4a241e010a0cde0df5f,0x19c7fec1b6a798bed2b5,0x6d059b180d5cef4ec9c1,0xb36379ce634e60fa3002,0xab5e2def2fe84edd5657,0xcf68d179cb86513e07f2,0xa602e827cbf7bc73b6ab,0xe4f2decd2739f6ab8ce),(0xd0cfa97d817e215709a8,0xf885df6a1ed2919d9582,0x3ce1116c5b6c4d769e33,0x57b008ce443daf678ee0,0x6da3e494e0181919886c,0x75da1337969ee8ccf210,0x1733cfa9c8c6cd61a46f,0x37f46548bb01ba285d2),(0x1b95ff48c1a3e4c633d8,0xc8edf3462d3c614410b0,0x56897d2b838b75e05809,0x86c552a2fe9505466b66,0xc504aeb6679b5ea15a77,0xc9a6f1999516c1ee0512,0xb50207979e3bfa1fad65,0x959ed0cdd80ba22bde3e),(0x8b5341c1dd313dd66fa9,0xc603a3bad35ed9e89776,0x2e70554f1daec7383357,0x19f3d919681d42c11174,0x537db9683e8d56ec17c5,0x34eed7ebfebfd5af0ac5,0x95115b5c4788c17f2ee6,0x645c47063130c04690cc),(0x4217a603647883797f66,0x437869053c90e818d5c1,0x4f03d7f70364e6b34f92,0x3e5715ca63afd9f1ddd9,0x3368c14ea902c0cd70a8,0x94c1e29a21f7e58c5f2c,0x90691abe41cc4abe2448,0x2c1d79d12cdd8a8eb95a),(0x481ba1ecea4c3800e293,0xf0e0af9ba010444a3349,0xa5f704d6308a7c9f909d,0xd2793589b4e182460866,0xb00d1beae3d44c5374c4,0xe23cd8ce1fd2f8ec5115,0x16168fd8e37a1a58d7e5,0xe46af41ef3a6598a2653),(0x86c26e4033ce66abd82e,0x103c6d9df98990fff47a,0xbdf3bc0407db216f55f6,0xf77e744c8db2e93d5523,0xf28fa60cc4a3746c863c,0x47a48f25e45872eb8bed,0xee202fb466cc7aabef43,0x6583c797aff60a32d11b),(0x3000bb6d3b82bc49aadc,0xa85e3b25e1f03d541ddd,0x2e527f4e006e00986531,0x12801ff5912c3bacf542,0x2d795a00ca9f6e40058d,0x3dbbc3fd20da86011717,0x67e19dc42694a0dfa982,0xe4ad4b71778c5509cba8)),
((0x242f5c09b9f128e1b129,0xb6e631136ce2232385fe,0xae4cb4e0c376b2935d34,0x793f60981a4d12e8f884,0x39b1206a1de3dc439e45,0xd07e2795734c67ee6ae4,0x6f6f4585bb10a7c7d565,0xfab1143479ab0871d2ca),(0x93301a37c7e1411825af,0x7ccc208c53bd2143aeaa,0x99b47a7dbd33289d1beb,0x9f926f9997f6b5ef5ecb,0xac2899b58d5a857794b2,0xb19c6b72c4a61fee4e6e,0x198d621780aee13b5d86,0x7a3a26292e7fc826de5f),(0x6cb42484b308d4976723,0x99d8f087a63a4f0da105,0x53832f1c9500694480dc,0x55a8f501e5e8e0622e87,0x5524a57820489cea0255,0x7784214802a8ec1536ff,0x20bccf8561768e5464de,0x98171d60d49ea5aef189),(0x83ec67830965bf55cdfa,0x2acbf66a7ed287c23562,0xe4e6c100bf37a9378872,0x8f336f8b06a69a74bc9f,0x261e7ed57efedcf83fea,0x1ca901d14625cbeeed27,0x526374c0aea20b91498c,0xb977c60341c63ba700fd),(0xf35261e73e7ae80721c3,0x6ce40daac7f117b9106e,0xcc65f2d1cbc87903ee50,0x5783c65326b76a9ed004,0x529f0d02ae6bb89dc76c,0xc58cfa2c63e09e95d01d,0xe0013b5e328117b568d1,0x48b145735f5a876a7286),(0x5333ac9694614df9cbcf,0x4a8cc2fdab74f2184525,0xe7faa61986b4a636b907,0xe0e0284d72d3be384232,0x74097916a6234a1d4919,0x430041843649d8f230e4,0x69cf71e98f92b56d05a7,0x27672982cdf5d472d101),(0xd186e6631c66bd2136ef,0xa27bfa28b90a9b086b5e,0x7149acb93b2d1261db8,0x6a8f12469e3b3652f09c,0x10e1309db65a4dfa02d0,0x29122f28bad9cfd32f1d,0xa44d8b206861f9742487,0xce88e3e96d50ace86bbd),(0x1823625bb4c5dfa2663e,0xed32e93f2cc6960f8e2d,0x1e86889acc355af327ea,0x33c21a81a9c9d8ab8c90,0xecc254cc5866fb556ddf,0xf002aca4e65466945b2b,0x8081bd266e77ad04e6d7,0x201fc12803f3a48de527)),
((0x9f83d10a87d2d97b4dfa,0x1ecc82a1bbcb8cef1779,0x8d9faa382cb1b6c719b9,0x88ecb3852649f9e9d611,0xfb98d658d119a8c69f2e,0x5e36a691963bc6ae254,0x6e8df1719bf9a20dd7c2,0xbd866b9bbab690a5aa32),(0xc6dcf3768067112add13,0x5051d6d3805e4d55b88e,0xfd23256991c6565839bd,0x9c724cbaf88ffcff0bda,0x41e76e86c30c4907b92e,0x2f7f219c2526530f6adc,0xc0036c6579144815b2f7,0x4fa59d0252f70e415486),(0xa8d14162d5289e6fbbbd,0xbaecd6f98f64ea698f37,0x6ba045b11a2453355fb4,0x2b12ea0fa755662739fb,0xa0e0fb573d8cabd4c95b,0xf4a902b2fbcd1b264580,0x36038cc381716d6fb8da,0xe13aa3a924986d62dd11),(0x37e5cb14802bebb5e42b,0x4affe0ad363f8b46461e,0xae8f0f685cd2af7923ac,0x32796f712645d5d4745,0x218b7fee7a77245dc16,0x960d614153c575eea7fc,0x28134ea9675f31ab39e6,0xaeb59b50e20820e8e7e6),(0x2e7eb5c7ac25b579d6b8,0xec44ce3e70453e7694f,0x94071b8c826997fe3f5a,0x59910207a2c15cbee141,0x77720a6a0b6167f4486a,0xb1d5ce94df31dfa2dc98,0x4def528094c91a5fcc09,0x73e780c3adc37ba80620),(0x4ec5a885994605a44cbc,0x8039eabcf713780afc2d,0x8bb91c0fa954f9256b2a,0xc378484febcf01851853,0x12e9cb320c069548c6c2,0xc13f1d396cfc741c361f,0x6cb69156d6d53a256c86,0xed8a1f949d5d4f8e6ae),(0x5ae421a54cde4befc5fc,0x81e5d71e1dbd6af24be2,0x64ce90ae0d4576c2dbad,0x7ed35cb33977cfec3e72,0xca9e90e0c59a1353d893,0x9a75afddea333bf70c5e,0xd18df41018d5a96db4e9,0x85b86705f46aac8229ac),(0x91e3049bd34a8febce38,0xf15d12a61f185b44b3ef,0x497b183e1a2f75db9745,0xe052c572aa8aa50e576b,0xef1ced5074035c2de90a,0xaa817b68b40ee5db33b4,0x54b9e80f08875ec2a7e0,0xc987c4c363098bde1886)),
((0x65a59bd84c25a7762d85,0xda3f5dfd42ad25986527,0xbcd198f94e5f420d4c41,0xcfd8d56aeac9b0c86330,0xc9d91b0175aed65f60e1,0x5ab20ab29da1a0455141,0x3debf805ae7b2702d12b,0x77e3b6fb051e5f45dfa0),(0x810f321f0d18aa7b50d9,0xe1a651bebda6437278c0,0xae8ebc578d8104bfcc74,0xca1db565f74bb9bf2adb,0x4b7e14e3249bc1b52746,0x778b26a900c3f84f5792,0x4272f1ed9b2537f4da2a,0xcf7f290e69083b0e75c8),(0x8f5330fe6153d716cf25,0x57b6f1c5cf7e2a9fbf61,0xbf5e658c3559fb99a21f,0xd6bb053c7aa53ef0b72f,0x2520d428802823c2c2f6,0xe6d2442fa6e22111ba4d,0x49a42eec5e6fd41d3b93,0x2be3b23c33b657e07830),(0xfa8500576edb1f6fc850,0x3ba7d2baea79d88da5e7,0xff9a2dbe1a47b2055b2f,0x421fe54c1af132fc3a7f,0x37498634507666c00735,0x9d81c799f2bf915b14dd,0xc6aff68e20ee5f624d87,0x53fba959dbba74f1526c),(0x15176eca18cbf3091d86,0x62dfa85fea47cb00c4c9,0xec94eab986bf76bc38c5,0xe102af11368138bc19b4,0x44d2f6b1e33564c28ac5,0x3c37f2d310bedb0fe9cd,0x38448d958c153be0248c,0x6a5015874470a880d3db),(0xa7abfaba1b7cedfefce0,0xa2765af8a0a35c327f0a,0x180f902f5ef0b07e263b,0x4d09ed8bfbe156dee9bf,0x10df4288f9d7ca1dd90b,0x97101c2d8406f969a683,0x9fce21a2281bc8892dbd,0x8448831063acc30d35d),(0x3ae1d318e2bc682a74d3,0xb4b7f915353e341c7ac4,0xe3cba524a091dfdc8fd0,0xdd0b02e9f679cc33af97,0x28346a07c28600b4549,0xaef6b757082f8d7f8aff,0x11115fcfccc9e09585fa,0xa9b9d0a9ac93af53738c),(0xe03653596c781b9d37e6,0x868681ba04f6698b5237,0xcded809ec934a81d5a56,0x8f316cd938dee17731bb,0x4095fdc42a5c076584f9,0x5ee6b62f0dcecdd851bf,0xb05d090f1d26c66602ec,0x76e50e4d2ab048dcfc00)),
((0x5cd09d38342f3066efea,0x53660458a43598b248d,0xb30a20f1136a577695c9,0x2c2189bc556e36bba3f8,0x792400be734a37953d0,0xb67ed753c2724f3e7b43,0x55007dd807987b41e46f,0x716ab049ecdcb273e04f),(0xc977674659b255b80bbf,0x9b75cbb73bc9f9561c89,0xed50ff1be16c0784e9cf,0x2728d06b5739d0bb2ac3,0xd63e3d36bf24a7470308,0x547fb28875da23260bb5,0xd1c56cc8a51091e97fdd,0xacff65f68bd061dbf8c9),(0x8c0494938200c8cfaf9b,0xf92b6c8337f3e718b1db,0xdfd6a36d9ce58ac500c2,0x7d65804fb69167c5eca5,0x8df62b2e35bdcbbec8e8,0x816bcd78976a6bd7b94,0xfd2db7c3573b2072c55b,0x1dccb53aa573b01ad3ab),(0x9d05cb0440e5acb8ccb9,0x977c4f40c748a17f3dac,0xdc9305e4718c791ee391,0x422cbe81c051b722f738,0x44c81b6b69dfa9d41b1f,0x6a0411ab74a9aed75efa,0x9482f256da61768ceee9,0x623ad27adc648f74a97c),(0xb9c17b0865fe54f6049,0xd9af20f768e9b4733dc1,0x6112fc67e7a8c2ec8e49,0xeeee819e879e65ece725,0x923fb1b876cc8c6a4107,0x1bad7d0fde6808d6718f,0x11a56b2713e26d0a6917,0x9b1ae51d3f21096f6cee),(0x76a99015c65bcfd43f28,0x17808a64957b4625de65,0xece84c81ac54fc8c0c19,0x16c019a5a6b572322533,0x146aae01b842a9963af3,0x58ca3ada60986d90f6fe,0x628e9e068caa92a6e530,0x805bcc0519f966c0b6f9),(0xe7ee1d16e73f51e521b5,0x1025f652a73d5a4c6aa8,0x9bae17298c21046aeaa5,0x103cd50a605eb3a26510,0x4b53098b6be108507476,0x4a72f3bcdb0a73931375,0x69df67f4fe36f25daee9,0x4397f8c3e467db681113),(0xf18ebaad7d77cf0ded10,0x36a0461b68a12fa24212,0x3de27c7bf3545d5152f7,0x10d2f7c8031003f09541,0x46146a99394894b78999,0x336afe1dfb44f3368f8e,0x7bc7c3c8631b622ec3ea,0x51988fdfcbda78f9d18e)))

def page15 : WordPage :=
(((0xa7a1e161e472b8fda2a3,0xdd2fc3e159b65c05773e,0xc5188d804c043d1fa9ac,0x9ae5b6357f2795fc576b,0x44087544450e33c5feb6,0x5eb9ca2d5d8c322f6883,0xe33832de14b666bfaa6d,0x76abfe219871eb533acc),(0xee3157d64bfebafe022,0xbc85e1ea0a280721d20a,0xaf76ba00492e0afa689,0x6b59a7af35f371f98f3f,0x6614bbb280ee9075e463,0x1a508d23fc7ebd2c3650,0x3be1bffebd40deaba4c8,0x5da49c2a4da714f610c),(0xa9b3bbb534a15f921864,0x4c18342ad39b6169a7ef,0xf8f8cf383622b854c212,0x8b6397495b2df9659881,0x241b7400973d3e9190f7,0xdebc862c9b45794f13e3,0xeb592b8ca1d656a58ca8,0xf3128ea2fe5fe9a7fe5c),(0xf643572cb4ae20aa8247,0x58f5b7973374462760b9,0xb72b175afb30ca1ec814,0xe58420f7bc1e8b0f6ea5,0x314a876d60910122807,0x170baaaf1c3167380a6c,0x2e2b1ab60f12d09e0b7,0x85b2c1db17c06616beef),(0xd367f3f8448a6b6d62d5,0xb1df1f9034a9ad036cc4,0xffe44ef81b2bf5cc3399,0x41e4a9ab245127dede41,0x97f6faa8364adccfb07b,0x7b5bd99a58e75a89b920,0xb96872e5b1a52facb466,0xe672644f77888a6b043),(0x65afd24801628953d2a,0x81fd17d5a3abbf0ed4f9,0x81ff5858b7c8e3452afb,0x705d7c2f23176ee0172d,0x517e25c9551ddacc6285,0x2059c360a8d8957536cd,0x5500a14f97707079eb4,0x1bc44728f7bd1e1ed62d),(0xc541a03932dcdde2d82c,0xc257ec3dadd27975d5d5,0x73a18660d82c46d537cd,0x89aaa581722d42da2458,0xda1a5745f3e9d13037a6,0x6942b454b89543d9f298,0xa5bd0c99ec3d4e954067,0xaa77777c1e28d10fd822),(0x6c7fbf3bf061986426c4,0x6e5993805c88da840656,0xafd9686c49585e77b41d,0x65ba666d259159ff3f1f,0xbdb9f5b4bc358a04464f,0xafff71fcfaba70ffe6da,0x6d091779ad42553a527d,0x91ffa31c84b968451927)),
((0x4f5abd5f0dcf1a14b2fd,0x1108340f0c2775433a6,0x862d0293802305bef5f0,0x14b99ab18f8582e68f99,0xfd63e74c744e41f1f823,0xc2355ed45bfd9f949264,0x94fc7e2eca76bc637b65,0xa20ab1ee25b6f137ecc5),(0x4856c35912c33ebb9d65,0xc5a1f21dafeb36784060,0x782aaa8807c96c7dd837,0x6fb0e539f26218649258,0x67bc9433d17143597e6,0xdb68bceab080726cf6b,0x50b2380e7b60effee2e8,0x9d2f9e47373946498ca9),(0x87cb7923dc9555507cc4,0xcc13b705acec74bcb864,0x812de21bd616251709e9,0xb59a2a3944e24e76e857,0xc520ac97e35e7b765688,0x5afb0f3e204987859ab8,0x473925f371fbc1fa5d7d,0x45b00cd228d0f5dfdfb0),(0x873b1347f4207c890626,0x9733d08737d6bb9b150b,0x20f71815b6896badb1bf,0xdf89c1f8bc54797daa22,0xd26fad462a6030042098,0xd4fa8b98d4f72ea0719e,0x2080209ce67a71ac08c7,0xc40647de32c93e3262e4),(0xbb5329ac0d14e5cdc2ee,0x39abe5be7964712829a4,0x9656a637f4b3efca1228,0xb8c0c5da09d3cff9335e,0xb9efce0d9f3099d4b6b1,0x1dfa27918c6a37ab0bd2,0x60c6d97915b8cf381eb7,0xc12f950195d60d8b4690),(0x5a425f45b52b9f83b5c,0xe7ff16897917ae046333,0x2d735401ab61f6b7dc56,0x19492235f4705d21d6d9,0x985e1acfcc24c65e049,0x78e18dd21e218fcea691,0x79080a93799f5502c0cb,0x262c53359c593e638ddf),(0x2346647990130aaed56c,0x25df573dd5f66529561a,0x1d5c2bfe950e5ba10d4b,0x74f1a0e832ce127cef18,0xccb2447354718203f42,0xcee44f5d177a45b1db9d,0x9a445003c45009cd405c,0xcf25bd12def6d118c5c1),(0x76a09cc0fc006f48c1ec,0x66b778c1e9ccfb2f71ee,0xb9924249339db6944c6c,0x4c5eb980276b64608b70,0xbc92aadabc03d1366cd7,0x6f3bf57cc08c42e408cb,0x8ddd9f12f8125edd51e5,0xbe9e8c8693fb61b831e6)),
((0x93b6f8e8366dfb3a76f2,0xeb5d07d820af1de6ff91,0xd4d47c561afe998ce1d4,0xe949fc28b59460baa41d,0x56fa9341c36088f2cc06,0xcf8049f8b81595ae58cc,0x2ee86ae10f13c624b2fe,0xa019201e38a2bbdbf474),(0xa569393bb940b57aac00,0xffe0b1bd54ac981af205,0xa382797182494053b4c7,0xe43ef4ef2d1b10667f25,0x5d17a24657209c4a8c55,0xe1184d9a16ec16872301,0xa73c4d3ec366a2416b4,0xa1e2b9fa2a2eee43f8e8),(0x2472598f8ddc23f92c1a,0xea111e9df381f66244b,0x3601a193277d97bf82bc,0x861b34b1bf09ff048e3c,0x8a63c38468060539dabc,0xcbe1aeda4d9cd7e18c27,0xc854b65bd7c322dc17be,0x2d28a590b4e2514f1772),(0xd785c021ab302889f7a7,0x80f7bb8ab16cded3b86a,0x52c0cfb73c65dcca2135,0xd3e26503af70fd10b475,0x5771b2e72a7f5771fcbb,0x3eb0412b47c7b20f7cea,0xd1496d46d8cbc4d9c831,0xea7e455e8fbad458d3e1),(0xc73e2edb6e7df6700e2c,0x83b2608693dbd3cb001c,0xdddf36a452627f5e74c6,0x452c9f76d2b3dd678bb0,0x9f4eb38712c32640d202,0x43ef5a1df4779b486737,0xb96d65025314e81f60ca,0x84ad4ee988c4a7ade1b3),(0x9e15803e3063f95737d,0xc4e7448dec0c2fc2c233,0x86b0dd0f9dbdb2d5f6d1,0xde881143a8903732c022,0x81a9f103184c9907d3ed,0x74db3777b4b4d33906a2,0x73c8d4afd51f6afbe64a,0xfe45d67086611fd67d39),(0xaeea707792e8c27b8ea5,0x71cb7000da5f6ab18aa9,0x81318d55bc5781be3859,0x2db7201a136cbb75dac6,0xf5cb722b9d2bd5b43f37,0x146abce11958c03a6b41,0x2ed16c56d25e677a17ad,0x40c700bcb991805d5509),(0x11ddc72172a1aa616d53,0x218935392a84ebb4d763,0x906c030c03b0cf004004,0xd0079bb3c368fbc77f7a,0x52b8000d95a14736fdcd,0x3f37ef98a4b84e93cac5,0xea367faed268e2e6154d,0x607270e4cc65dca31afb)),
((0xbcf9fb1d322d5ad34141,0x84c4efa37f3473aa8166,0xb0f0f514316cc451c0c6,0x7753dbc37abe1920e817,0x6b65d3bc4b121b2c13f1,0xa10d243625d67229037,0xe09eef2710ed1bde14a9,0xc9eb087a80b02edcfba9),(0x198a00cbe3e01abca253,0xd842f2d9d7532f8b996f,0x629353a7107b11d0b938,0x5d440df60f158f7846af,0x78b943822ec74f71a47a,0x3133e0400a95418deb04,0xc7217dc7b21b88af440b,0x7bced47ea6fcb9826a2),(0x7e6b2a8b40b1326b3679,0x58294f6a822d9713345f,0xc8533c0fef311fea79eb,0x7172c4172ac55798d4d2,0x5249ed8782d47a5f67d2,0xd7f3df3c619b6bde2bb9,0xbd8d22a8a40346dfd9ae,0x71301202b2fa2b5a7334),(0xa7ca0fe0820152097a20,0x27de3959fa0a18c68e2e,0x7f463336a9fff2ceeee3,0xdb9e87d57ecf782a0fa,0x494fadb59701ad94dcf5,0x3ea4d1f17a895fcd25bb,0x554d7182ee05df293df5,0x6d90c1ba0b32fb40f28c),(0xf9313893d05855f36808,0xd1eb60e035e8204705e8,0xb96db8b42883e9206d9c,0xb980ffe8321be0b5ea37,0x5dda0ff68958b70fd6c2,0x61ee6cc223671f633d35,0xa1d2fff7e71698f814fe,0x3436b596b8fb7ebf6668),(0xfc5ee13f8955f933be2,0x9e66c366e47c46f7b1f4,0x6dcbf31698b36b0dcec4,0xc893c9980c8e9f63a8d8,0xc7f14ade3ccb50039e80,0x6f41f31cc6a32e935f9b,0x43826e2567020dbdac1a,0xfda00fe3308253a9495c),(0xa627ab190e6dd84d18d2,0xf4f347b5315bb44f76f9,0x816c281734bc3a14b673,0x380eb34da0ba90701a9e,0x434f17d7725608f783a1,0x16b7e26253eed20cdb3,0xbc6dab1bdf4c87823856,0x76680c5cc8f9f4ca61c),(0xa74e4a1fc5ec3922add,0x8bf7c5ed7caf6ddda12a,0x9ce21f083ee4bf996efd,0xe9542ae11be0f7836b7b,0xfacac9d1c9105f97e75c,0xeda4b6e21d72cfea85c6,0x9ca138bdecb6bd588d47,0x81762a21fe1d4593de9c)),
((0xdebbc1dd65dcf7cdf8e6,0x4817a808caa0e33ad35,0x99c80204df1896558c2f,0x533d3b638deeba6e9e65,0xe80865e5527228dc1c91,0x6a09e51dddd99f66420d,0xa771518ad468b7316c73,0x63fe31e06c638704a961),(0x8d3167a8c7910356830f,0x706b82f297b3166996e1,0xceba1d2aaa668c216ed7,0x2ad971ca5e39ba18afc5,0x7f0d0e07160e0f165ea8,0xdb2318c4172068d9551b,0x6e4dc2370e6c6dd31008,0x974634abc412485fa7e),(0x3465bda2fcef96914f00,0xe9cd7a5106c406cb235b,0x465c0724c24f1a3adf7a,0x2056a3c0b5806b9ce05,0xcf727f3a25a07d4c3f32,0xaf2151ebe2d40b574c61,0x401428cb72d8998bae8a,0x4303b0469782d3bb0b2d),(0xd63d9355846b6c9b9596,0x4ef2c6881da115420fde,0xfa7a966e7dfd01ce456b,0x93f89f67637d917db327,0x6d109d84051f8f61679f,0x49cf884b246004804e0e,0xa4ccf15766e75820da66,0xba801071a3dde4ea8893),(0x1e13818f075bf8366b9f,0xf05bc9aa0028240603b2,0x21ed1526e087d5f047aa,0xb284152cd5e698f6ed5e,0x74d40238061767884d4f,0xba429d770f20b100a88c,0xb3e064e89e3456eaad6d,0x5519d391c3d48819fb1d),(0x79f9c2dd6582d3505d5,0x7858b7472501bd9d171,0xcc86ff08ec073298a950,0x9170345ab621657a2298,0x8479275b8498ae72dc4c,0xb7b098f6223df1eb2608,0xfc20c55a34004d1816ad,0x6340a7b1cb7c6746c35),(0xcf43ae6930f9c0d7aada,0xb2edd52dddac5f966186,0x4d6a8750dd8a25af4e51,0xe6567477f72ccb97fc40,0xac9ce49f63d576cfd122,0xa6a42c19fa7ec46199d,0xcb5302e4a9be26193f68,0xcd4c3b1fea97e591c570),(0x161e5a5c5938491770f1,0xc42085da700b7c75efa8,0x990bf1dce45c21720a7,0x7ffa0ba4e4ce1578736,0xaf55cffda855cee332ea,0x694a46ae8150e0aa055,0xa731392c430de6461894,0xcf73d3431f126db0ec26)),
((0x8ee9d40b38cde6599a00,0x8ff6d44467f1eb578e01,0x2058337fcf5cdfad4273,0x47ec986ce4b20331cd3a,0xada0a2ecdda84ace2826,0x307f5a4c23fbacf6fe3d,0x9b95f25143a631ec3dca,0x1cafe3308967d17f3322),(0x7a5204ca2efc42721731,0x17ceb2977d7c654e7028,0x62241c9c009ee74a908c,0x78af096c88e08bb74a8f,0x4ba180a68273cd5448d6,0xe3da4e73f8b3fa18735c,0x9d18d77a265ac5c353d3,0xd7d53d720d2305992dec),(0xf12cd36e642a39d3d28f,0xb9aefbb761a98b47fee4,0x5d9afbfc0f86b38f83c9,0x4b51c9709a003864eb5d,0x81cfea7674afc47d2de7,0x8e147fa7f1a47875d638,0x7ba141f61c1a50ffd80e,0x1b3cae3d05f73a9d8a0a),(0x720fe2fcf1efbe269d5e,0xe5eaa4652332887fcff,0x89ce5dc1518daf470b4a,0xbbc3a5ec9f8c38636e98,0x9bb1f0e56c1d88a4e380,0xfc02ef3a968f82bf52f1,0x85edc25a83b79c4f08ad,0xa28d0971e1b10e53d9df),(0x489e3404638c0a485d0f,0x4ad895bd03247802b8cf,0x7edf5487c4bbe5e75151,0xeba7bf09f9e69256e88f,0xe41689094a076187b0,0x7d951638f6f6acc827c,0x497bad9aa70335926f7e,0x7e96437af3ba4145d65a),(0xe2e10b428e6241ab6867,0x3ed7119ec2df342c12b6,0x2911675f9c18801d6d68,0xeb9a16b8a969119d33c5,0xe278082ea5104d717a1f,0x6add16c4fb2ccb9b523b,0x456f30d7b1e0b886163c,0x4e118eac452994947bb3),(0x228c64a28917a54cc69,0x3ca9e49b30dde714f0d1,0xe303c46d05bb7d5fa108,0x6d25c38f237562a903c4,0x2e366c6e6fc12963cf29,0x5b76270b21bc33623b3e,0x89ff701b7bb04f17e632,0x8d0982b5dce48b7fb701),(0x327413e4e65656873935,0x5561cc630b7fa49c042c,0x44c69044cd4e2dbf9256,0x8449908828cb65c62e7b,0x3ec5ab63495f5c07ed2d,0x4721f22e090e0996e439,0x7ab9b550fa601b8a271b,0xc42a5354fab0459b658b)),
((0xb6de3d606937fc155514,0xc66a176de47f466aba88,0x34fa2dd9a4371a79522d,0x90dfc88830701fddddca,0xdf5241643814049de0,0xaf55648b2c9003c0924e,0x55fd922b63236551bd95,0x7dfd45296c52e820eaf8),(0x64ebdfb706bb56350238,0x1d072013999f16571aac,0xafe1687a0f5c8977a800,0x356b7e2722e4fd6ed872,0x50727a5862f07e2646ba,0xbcbfb47baed846e85f7d,0x640dd3e241962d163192,0xcbfc6b5848bdfaf9d526),(0x16f320816136f9d5447a,0xbc774db10cfcb6635156,0x98eb58685cde7ad72666,0xbd10b2edd55aa273c26a,0x8af09e362c11a248dfcd,0x90a03f8880515a3ecb5a,0x4fa50ea2bfa30954ee6b,0x284a12be1790a172cfc6),(0xf76a0b90a5b4aec032fc,0xea9e1a57a9d911fa4108,0x38cc65a26d057d35d668,0x220a560d78982772ac8,0x9abdfd3aeec03a8f9ebf,0xe4389caa1fd83effd0c0,0x8ba59b51ff73ad4d291b,0x91f0cbdf2880813adf9c),(0x6bd034dc1899edb1af09,0x6225ac68b0b658053905,0x79f50c89cb698542b0cc,0xbaf53c30f7a09bbe805,0xdc12060d73901dba7b7b,0x77c0261066c4af0189da,0x6868c36aad58011a4883,0xc66fe10a29e4af464ed5),(0x4f38aa44dbb5aba21e15,0xfde38ede876fdeb0448e,0x2dd497fb58e0e6fa9949,0xbcfd7dbdb831dd97b734,0xbe2df74104553a2cec19,0x166b09cfc9ba3eae5b8a,0x28168be4cb65e7ef8869,0x9efe3f82f752583ff13c),(0xc98d119bb91eb8d02ddc,0x586e0b0bd893292b4872,0xab777be327534ada0fb5,0x84cdcd6b2f39251e1b52,0xa1d1fb7376e40b532f7c,0x1afcd16072bff9d663c1,0x78a303a5f88b8e6bd077,0xcc57a5a715bba719a089),(0x31f312fc726076c79c8d,0x86650d52ab2d1df6f38b,0x12d9e88b2840c3077ab4,0x55586a022d7b2eb8e1b6,0xa200b8f3f47c5a11faf1,0xa73eaa34d39ecddac998,0x3985b67bb9fc4d6f371b,0xd8b5ef620730ec0cac62)),
((0x954308f0e023b626fca0,0x7361d304b2c6c8cb0f1,0x8ceb2186c9837a8eaa1f,0x6e273569c08c19f38208,0x2ef69d0d7e8e910035a2,0xb84e031d8439bd888d50,0xa0a19e3fb367cc2c01a9,0x782159b4653691f87fe2),(0x41d7b7c44efe63a8b2bc,0x4635f7db7f43fead8738,0xdd16a5814e73229832a2,0x8a6bc5ae57bdfaa9cdd2,0xc9ced079aeb1a95b366,0xbaad71eeb9f24e62a271,0x82fdb9bc970bac0deab3,0x9936701e2d99bb09bae),(0x51699a1d3b967ef292ef,0x6dcc38be14a774d3ed46,0x3e84a46d79213ee589ba,0x83bf6fe2072b4351d81f,0xc8e90a935345facdd0ee,0xf75f4b4783b038bd9983,0xd0a693335aec1fe6307b,0x6e360bf6def269d5ac17),(0xf490f354a3d0bf559e55,0x8747a6254bc0a0a341dc,0xcd69870a367f3a0957b8,0x1fa01250bb2aacbe8b0e,0xf990f57a17b1c9623000,0xb9c9e1ac64f5f36ac891,0xeee60e6675d659f330a7,0x1cd08e0b09e0936707ad),(0x7d9f1f92f5c73fcd0628,0x9fb796361184e10fba17,0xfb6558816c0f2eb0d365,0xb09d2d3f0f96e477c5fa,0xcd7b11ecdcce5b26f4a0,0x8a03f4a3250dace90f21,0xa7ddd83ca179b5ef8611,0xe496c2682b6d1249a28b),(0xf1403f2832ec8088bb83,0x1bd1904a18a5997ff167,0xc16589c9ba1a97a5bc3f,0x9234c0cfc0e6b9370c7b,0x8182f8bdc9f9b031f764,0x179364e82706ef9f135d,0xe1a8a85bd6e7058833a6,0x7bfdb041e4d4bc9639b7),(0xe02e01b8082f4a2f2e57,0x430c9b784cec49fd4884,0xcaf13d81a8b486d83bc7,0x1773ca46362708531b16,0x965425ce7f1833e946ce,0x8a8d7ae2eb4d649211a7,0x9ef56a3e2e0f27363ff7,0x847d33d52a23fd592c49),(0xa74afbadf9f637675467,0x6f6d45e9ceb57692a00,0xb23d6d60df207e280b26,0xbb11832d9aef989c17f6,0x9128bdc5ca5200e6237a,0x636fd61605a2ab9659cd,0x2fdb2a1773e10cdbc739,0xb232164313cd47619bd6)))

def page16 : WordPage :=
(((0xe8ee070bb2e7d03c1bb2,0x8142e05daaede9255a39,0xd578d1ccaa4832547ffa,0xcbad4b96625dd6e93d97,0x8c103d2e96801a7e284b,0x4226ab262feb42ebfc10,0xb560a7f4cdfcb5d470de,0x7b458489e9c2d73dc014),(0xff2059bebf25b4e95db7,0x791a56f375bdb262e2d8,0xdb398a88ab622e33dbb5,0x81f044849d55739d4487,0x443c2877dda3771db34,0x9a3307f2caacfbbfc838,0x2e1de5056b7eda5a4da5,0xbc00eebaafaca61fa915),(0xd4e31e659b590824e447,0x4925f5b163a945ff8225,0x19558b8059332505bfe7,0xa873b3214764a05d4aec,0x1e68191f7f7647544f0f,0x9c66d0e2d3566fe6dc35,0xf8739864edb71590a2bd,0xdf841ac3863d320fd57b),(0xb8a242278eb1472d67da,0xd5ab386617199e1058fc,0xd901f1e2fe756866bce0,0x3d404d0776d0403e792,0x7eb3ee97aa8d3b7148ac,0x2562867e95276df42ef3,0xd26d9a6fdbf32d8fc20e,0x5b9ebab2b15a6f44ba85),(0x6a7886135d49918dd217,0x236dcbcccbedfb99b5d3,0xc2d98c44559d75bb3b52,0x2f3a6f9469b40422cf21,0xc8b4e8181a681ccad026,0x1bf1c1db516a546a7b01,0x5b717b008d41b69a5d02,0xc101882b204e0df2db40),(0x2ee69b268327b541387d,0xf9d404a72c17889eb7a,0x5ecea69a608d46ea2498,0x2445aa38709b33e159f5,0x284f47de0a36f9e62593,0xb228e975aa3b36278a00,0xd41e68c9d08551f912ce,0x62edda63d7dc274f0a0d),(0xec3b2c07e6c32c266bc5,0x7493f536b21a6296af8a,0x4e2e1e0c30733fbfa976,0x66d5b25728a21c767b33,0x910c6c001738bd713ad2,0x39575324b7b1664f8246,0x6decb25433e725f6b0b9,0x537c96ce99dfff92d664),(0x216bd6efe2abea85a6b6,0x2bb5a5de630c5fe01b1c,0x5a356c4812b402b5102f,0xb90a1e229b9620f3192c,0x2e87317ea2a0216348cb,0xd77c1b8984e7ad8b31e1,0xddd89ed75dea667be987,0x3220470196ade0457446)),
((0x6f864a3b6e8ad9cb9f7f,0x48a31bb04378e5e4fade,0x556364f8907dc381af29,0x6fcf3971c40988d138ed,0x71980c1da97139261c7e,0x5014f21dc77b05ccbbb4,0x61a32dda024a38340eba,0x6bd498efd6d499858fbb),(0x69d584cff42363fc353e,0x521dcffbbaded591a81,0x6780c0d0f790f2013ba3,0xed468f47b32e72ad5806,0x76e9c93bab27dddd8893,0xf53aa1b0dfe98f252d2a,0xb3770598f68e2ed354e9,0x4d3eb12690d689aafa71),(0xdea3fb6bbfd4b4f8af68,0x52bc3caa65de59c86adf,0x3f6618b1480596917da0,0xea18ee4b77001f8b3a16,0xeea9c2b1e1c10b6538ff,0xca5a35506291990117b5,0xeba0fd01a3c50e3b87,0xf4a47299cd6378ca1a6),(0x95c39abd2096e1e1bbc4,0xb6f91607d598d5f65ac,0xa590b0550f1ec4b92282,0x2e897490bf0ef18830cb,0xc4217adbfe6d0b546397,0x44d99be017672193db20,0xa94649831205700cf8,0x6f9a1a6def7b64033dad),(0x2bccdca647d0019ec6a1,0x14322cb03c3221be3baf,0x8df4d36ccf1134e06635,0xa69950fc631b573e762f,0x19e40eff27cec7055015,0x1b1a34287e403d41b26d,0xbdaf4f0459e4741b1ac7,0x746d3752666d85ef8a2),(0xd35bcfae20ae8500423e,0x814f4e3e56ef01fc12cf,0x75af5f9481a7852eccfc,0x83e05bffb6c4944a3a4b,0xe31cb6b669200bc9aa9d,0x8789cafa7f445209d49c,0x6d4fd21d59db35b6dd78,0xda9274babd62b3b97873),(0xd5b7f427a361acafdbcd,0xac4d30f2a05bba1582dd,0x4273a277b67efd20c770,0xb2445a8bd4eec9f4ed45,0xb81747d6dcb2a5d130b9,0x6c8012b994976f3c812a,0x11da4eeb64e1c414a47c,0x9673b9c67ebb10de3282),(0x65c70e6925207bd4d020,0x662041a7325f4c804d75,0x394955ac5d23d18b4e1,0x5b3c1d97b0f23baeb75,0x76f026d9b1afe7b4ca10,0x14188b27f75467f0d8af,0xca41e2f2a85638513d3c,0x9c2fae5db9422be5039a)),
((0xd8175f2bd86fcdaeeeb8,0x13652a438268a9335ae0,0xfac16438a64aa1bb33c7,0x5c796fbb41d119004ab4,0x6503e53ddd4e64c082c6,0xefecedba81bd90581029,0x4cba290303e317e0fc17,0x31d5c6437cd5291e929e),(0x3ff66112cb01b0c56f1e,0x2816947a8aa3178bcb01,0xd4d7d9822ed1fa6aaa2,0x5957a67769696c8aeb39,0x45cf506775fc553c10bf,0x7dc2169af57251acf486,0xc90c00424c68e94196a2,0xa9e83474cf3ea5216c1b),(0x362dd38f64ddf3e8a753,0x1f71e8eb04288f438e95,0x221acfda42fa8e836950,0x3fad1d2c6d6162d20e80,0xb16a47257cca95d71165,0x5d73d36493bacc065767,0xb32482a3e5c1d658fd8a,0x96cbaf292418f802c890),(0x625a7d0eaf00c3db53c7,0x2de2a3d4ee2b819c86fe,0x829d0f41c911a9bfb89e,0x498f087bc195a4e16ae4,0x55d61c305688f5226f01,0xefd059ba9c07ff6bd019,0xc1b2c1f3075a80799fb4,0x55749240d9717d00302e),(0xd8f6ed1a2f85a4cee427,0x90829110f2711ccba0ab,0x825a4339d0df01d30bd9,0xc6d51f6e243f8a64a7a3,0x37e974cf6d464ff5c5ec,0x3beb8be6e8446b5684d2,0x361b3c8bf5c6591e3e95,0x97187d0b87fe2af132f5),(0xfe80849d736bf11a35b6,0xf72b08476222e09a6c39,0xea6cf9b94335eb5c42a9,0x278d4b40f535b600c98d,0x1a2132a5d458a48ee55e,0x819c6f2ba8c7ddd300a6,0xb1e55994c2236c630f73,0xbc78bb87f36c62a35c3f),(0x257aee45bb4c05c387c8,0x3592244d5abd64a31d2a,0x36b8bc4b42c10830edfd,0xdb169785d77d824ba86f,0xc5ff98924f6d1394a840,0x7726cef9339eeeb88b37,0x1400a0a832cdcf4aeabc,0xfa2ad026b6dba759bdc),(0x8bfe5ac17432f253325e,0x84ff53932cc444a8a58f,0x3e8af6553f906d0aab8d,0x37e5489bfa710884c26e,0x147d431049f593cecae4,0xb1592e29f9a0d44d244e,0x535ff7bb8e06b40be750,0x67fcf86c89a1957d2157)),
((0x1b929c3d912c763cf48b,0x38829647c243cb88d295,0x49b9c7e1ce8ce430405b,0xf47b97586f9ac197b764,0x7eaa0e3d753dba9ef0cd,0x8ea37b0a04e9318ceb73,0x4be0b97371d80720e14f,0xeda3a1d410537b437b62),(0x290200d14abab94a7444,0xd10338cf4bacfa160ecf,0x987b7e8b64b2dbd8cc16,0xecf7a262e97a7fc6e784,0x97e5a7c3f104ced51613,0x4b32636a96b5f858cfc7,0x16cb4be11678f3672ed9,0x84b2b26ee1bb8ec1d262),(0x4213cc16318e6bea30ac,0x3ad0e048228985a463dd,0xdbc6d5d1ece6aa0ad743,0xadd93f1583848cb9d875,0x6d2bfae7d8a55a49a310,0xbfa2d4f7b12e4c6b4cdc,0x4ec79a4bda64521da810,0xdc60d714a873b779d60a),(0xd1ebfb649adf7a57fa9a,0x3bafd88ef30814006645,0x25524f7fa8c5bcdeaab0,0x876b37ce5dd9097b5dae,0xed8c306e590011cd4d9e,0xcfb40d5dee921aa176f7,0x6f1f0d95050405bbf667,0x72bddc92a06115b40af4),(0xe59d218703bad8819299,0xd4e8d1b3e3cd479d1cf1,0xaa6095471198b3c9974f,0xf945ebd1f1fa92b27b68,0x7225fa4be1eb874ced7f,0x2cc252729c124a28663f,0x1f4807d0e5c7499a3ea6,0x7c1e064c943b5a20c231),(0x17474b55dc4ce51c3fad,0xc4096616211847a28270,0xb4d46fe27f6f0775411a,0x70644197051b2a253faf,0x5cc5de3ea794f393260b,0xd808110fe2b7b5d04c,0x467e7f1bbe8cc2ced876,0xb2aa988cfee5ae294a91),(0x2d290a0d47aed98ee9ca,0x515e17e02397825a21d4,0xdda0c59533cdd57ba0cf,0x6a7c24fc469817676921,0xa8a8eca6c73b9b8ea25f,0x63c1156519949fd14f32,0xa52204d112ddceb4894,0xf8127df0cd0448575176),(0x9bbc6879915ab9f4512f,0x7fa57ed0d1979d94b4e4,0x2b7daaf7adceb69bdabf,0xa9180e81efe0fbf2ad69,0xcef90079407a4d3aa86,0x32ba3bd179bc8cadc07e,0xff18e8eda23d98b46f21,0xb548269808742b3b3adf)),
((0xfca284ed4d0c2967d191,0xf644750455330f641fe0,0xabdb66dbdbce9c681166,0xb25a806007bcb53684a,0x19505068d68f9cb479d0,0x7529965eb969ffe12655,0x1a7fb45e971a5633d28,0x58e5566639ac91594b5e),(0x337cd545502c9a27069b,0x380eb12d350575f943cc,0x2232bd18cc83e6019512,0xa79032a738722696e22a,0x1b22b6970f23302e3ec4,0xf6f154aabb62b3f963d6,0x92a4f8688adc0325568,0x85f96abb75916b9a5f9c),(0xd02574cac23b08f824fa,0xa97e78e9fa37d7082816,0x4b1d78eaa4122f83b3c0,0xbf03fe726cb6cf65d1b6,0x1b9c8f2a771f491218d,0xb4bb5319f93754551a53,0x83ed0d460a25af66dc69,0xcb2d380a0d4fbc5e3dac),(0x8f934543ee1fa8a0334f,0x84fb428641f9ea245cbe,0x179a028020bd0a48ca8e,0x3b2228bc5f344d857c4a,0xbdf1c87d71f8d1965f58,0xa858f35b4cd275d2d29a,0x95f4493c5f9f6cd9ef5d,0xd58f628b45511457f9a5),(0x913f8c81b29263e18761,0xdd44eccb1300085e1368,0x22ee300b1a9a89c076b6,0x2c4e899dfec1b4718f5c,0xcccf0683a6796925e82a,0xeaf5daf746d74fce31cf,0x35eff9f141c544df13a8,0xa55d9e04b1bbf9362b59),(0xf6376a3f1d1d951aaefe,0x943882d9dce9ec94b0e9,0x6586b75743f2f4fa7042,0x1991e9f636bb8cd2bdd4,0x7311976dc5d06783b472,0x5d6bde53e7f2ade360de,0xe1a18dd81c9127ba4ad0,0xf37a52f0c293bcb24de0),(0x1d973804fc6f049f916d,0x76ad6efeae74d47054f6,0x58198535246c65fd900a,0x14ac119479f5dd029b0f,0x2095847461af29368913,0x764495d96816383d7ccd,0x59c7ad7679af166773a6,0xdf8676b75420b38cc6be),(0x88cb7f592aeb0b4f7cda,0x203410ad6044aca77915,0xefa508955f69b4834357,0x3def1d6fcdbaf9ae9dc6,0x216231c2c9134135862a,0x86e5e8fc78764a7c1029,0x970952cd219425e26004,0x84ccce5da27d16f55ced)),
((0x57bfbfdb444fbfaca523,0x41f90c236b8215348697,0x68912d29757a26dfc5b5,0x3c52346755813479eea2,0x7c61891fd0c91278bfb,0x1f40cf303619abbcb25a,0x10036fdd1994eb8f51b,0xa55d5331eec633018008),(0x729c14b2d14f90f8ac23,0xeb5d8f88b28b1072eff1,0xefa62deb3278164c084b,0x909283a0ef8edad82d4d,0x45bb14ccb7064e9a0180,0x782bd0b25bd7d44adb5d,0x7a8aa0795e6e3354e01e,0x668f6988ac01a73ec438),(0xe6701c2148123261f761,0x7be8068d20c76a8f5ab6,0xe6220cd7c63473c2ce3a,0x2c9943dc42f84d84b389,0xf2b37aaa1e71423cb277,0xa544829dd450dcf196fd,0xc52f9a40aa5a3d129976,0x6e3fbdb30dc3d3468da4),(0xfd89550befe5787ca709,0x411c79e19102ed67a352,0xe8977172267a431cd2bd,0x615b984bddbd4b8b0f98,0x6f6f6009ba8ca4708b88,0x11cad8bc77b492bb4bd5,0x75eef822931b10dd773d,0xfb3d63475bd316914712),(0x5935d5de0d6414c08bc2,0x35012a81dda13b61608b,0xcf684cdf3c12ac56b15e,0xb9858fd955fc0d8bd3f7,0xa15bac0ff8d2a5abeb0a,0x51053a8b81bafe36fdea,0x5d2678194e434624bca3,0x2007cdba8122f72a11fd),(0x9aa191fd4b856a4881a2,0xd6aeeb6a8802917d007e,0x7ce52561b8d45728ddfd,0x332b4daaa21acfd75722,0x7d93163a4bb7523767a9,0x64c05c341f42d6e3c6dc,0xbf8fa66560ed0df55435,0x430b8243d5998571a78),(0xf5e343aa4dd70167a296,0x8be0504b0cf9fb39b1c7,0x1ef1bd5113dc427dedfe,0x73b5a132b36b70c3c996,0x7d01df7cc29650b2012f,0xd5bab5b227cd6c470454,0x3c1c03e3ea8aa6b96ccb,0x3afef8ccd8c1cae208c8),(0x395aa446e03dce361423,0x9c92e481aab81fec468e,0x9d1b0d967e4a6fdbdfea,0x917d2f98a3a752302cf9,0x714994b8f2c6a5033ec1,0x3499d6a7f81a74285159,0xe255e442ed6279682341,0xc7c1e82f0816f20b2284)),
((0x60b0a2e58d8a48f90b85,0xaeae201c773f5df173a4,0xb0658ce4f6801e861961,0x30376e8d62d43bd394c9,0xd500cc5c723023fc5506,0x33c2b7d6c3e46896b4eb,0x2a68939d3f39ccfc0ea7,0xf6dd1d20b559d146c6cf),(0x7b111f4231c92f34b3ae,0x1571781e5a6634bb76e6,0x9b617449cafe57e73ccd,0xb48d825d3d290e0500f9,0xd6082ce05f15ceedc6f0,0x21e6f8c8540a764ba538,0xbcd0959ea81de093aa85,0x28e59c402b6e0a358b0f),(0xade7532c2dc81672cef8,0x48db87676b3d6b302ce5,0x890a1cdaf72b5913495b,0x55e370e11ac56c9bf8a3,0x570fe91186958f9f4387,0xdfff6577503a5309a050,0xb59ae692767a86ea1ef3,0xe410ec6b6bb4e90ca0e8),(0x20af639ee23116b21d2e,0x56459e906f359562ea5d,0x772dc18bcf1464bdf90a,0x18eb31d3a5f3d6e7f396,0xba078049e56f010e1c0b,0x4895bf26c222d623adf5,0x9024cff9b8f7d9f9e085,0x63893536e42be8f52d9b),(0xc0574b52331655a89cad,0x370dd7ff8bc7874a5b4a,0x9d97a77a622af20d0f0b,0x66dd006e13422b1fb2e2,0x203bf117b4de3f1aafc3,0x8688540777796c51197a,0xddd678ccaacfc344e12,0xd76a59013453a4eaf455),(0xe3053637b9c4c08e14a6,0xd429065444d115491418,0xb5e15823ced363e6d50b,0x94df52c5ab4f14c5c489,0x67e824560505f5d5eb51,0xb8706b9f54cb0ff52e1e,0x7d4df87b84e17c63d1fe,0x2608dae5e564a5a95361),(0x2c293eda4fc57a1d06c3,0xf9262430b690cd12da8c,0x414d2463583a43548d64,0x541108bb971050c14b00,0x3d07599e07f31303db0a,0x517b65fbbe7966c623c,0x8172670a32c8548d301c,0xeaef5bf45159550f0ece),(0x7d6ee0647cea4921f515,0xf143b6c7721c89a1e00b,0xd91f21190a7e8cafe5ee,0x39dee31f0fbea8f6f4c8,0xeb17fb1bad0b3f9e63d4,0x45997e9fdd816f34e117,0xb32785145e023f999a22,0xfc59422918be331ab15a)),
((0xec56ab02b1c2e51409d8,0x7ff69ea3dae392f93315,0x66025a2ebdbf6b1e2c16,0x977ba8f37ce91fd56f25,0xe50b081e163f3ddb7502,0x4c3a465edb70704e0aee,0x97ec7e9fdcb2e7c6c9ea,0x40c1adabc667c3446802),(0xd337c4f1d2b36607393f,0x2eb80eb07c3cd9f7e6f5,0xe7bea183fd728e616213,0xe5925eeff8e33464132f,0x71af97d9e60f911b4323,0x779053fc43bc8b6e4f8c,0xe7f6fa3fed2950c155a0,0xa00cb9ad0c0499557b1f),(0x8ae3f9599295e930b646,0x42ddde31455ebcf9cd56,0x4a451a0511a95f73546a,0x454c397c51df41f5a832,0x6a947c974bd5590b2f3d,0x15dd5fbc8779e7b83e65,0xd763d078116209d11fb,0x40c83df4c71f6cfe807),(0xd6543cdc137820c351a0,0xad8fe2e9d6eb0ea28a82,0x6c3957b1720f319d8320,0x3bc6baace6b0b174617a,0x2332200af2532170cf7,0x24286695065b1170d28e,0x183a373d16faca9cd4a7,0x190441cc92364c65364f),(0x9e506f2ae1b5549068a4,0xfea6c1c1e8ab16b74b56,0xfb2cb2f3dadbbde1329c,0x52ff250e3ddf9dbc6a6,0xb2ebca2ff75d69a1b813,0x67553c4d6109404e3e89,0x8395f557c9ae289e2265,0xacb8185096effb8f30bf),(0xac81c197deec534d871a,0xb2290537fab7622c5af6,0x66c52b6f4b43e202efbd,0xb1e44673db7b2e41595a,0xc1e1f252bda069874d2c,0xe871cac5204dafb4c90b,0xc25af5260d45ea851e47,0x144c1b950fecfd785636),(0x9eeecb85be2d2eaf62b6,0x58c9370c0209b10bfbdf,0x66f3377f8428fa1df244,0x14abe7b191d4e61de600,0x4a8ef5be440590fb30de,0x68a604dc2bcfe7980cdc,0xc620a1b4ec47d0236818,0xe295a95ac9f66b4519e9),(0x2100c0d248aec05bc02d,0xdd9923991e6398e2571a,0x70a637728e49416dd3af,0x568c1728dfb97ba063b6,0xfa1f588fa12e0125d6a6,0x122f1da4acbc2b849f7a,0x2302aa34f1ee89e34e90,0xf9fae77fb0a2a65ab6cb)))

def page17 : WordPage :=
(((0x175ec25b4039273ba281,0x56a011d2cd65993d90f4,0xee9c65350a70236ee86a,0x7192d083c9514d0f9fbc,0xae264c56dccbbbdb863d,0x372896d1abd88fe6df92,0xa9cc08b1ebb394ef1983,0x6f2e14f32c4c932ed818),(0xddb91541b299094484a9,0x19be664a5a3f3504b4c2,0x4d8b7ec2d374923d99b0,0xdf3a76c90f35dd58f3c7,0xe10dd1ec3f05c8c30a8c,0x8f3c40bfe60cb8660458,0x518e616caf55cf7aea3,0x8dcd3c72bc7c782bf4e3),(0x640034681dd7c4668ba6,0xd8830e767a0478c91e2f,0x45d0985b7e2cc4e75ab1,0xc57aa8046c54f8c451f9,0x405e00e05f284986b760,0x8472a0af7eabd25947e8,0x9e052c569831c3da9ef0,0x9615ad99072b85b34db9),(0x55d1583e8d94b5410ccc,0x9ecfac196c9982cabd48,0x1bf7372e7ef1bcaa1449,0xd362cf8cd3c4563cdc6e,0xd2b7d29fa0ae0467e18b,0xbd4ba1f1602109aed5df,0x9d36afd977056abb4f5f,0xdd050658d4dbd4521bd4),(0x107c247c92aa1f0daae7,0x2d2a18a3aaae1d12fb3a,0x562b8301810b50cb014d,0x566ee3aa0e38435539c,0x989364a3a9b38689bffa,0x47abc61141b8f3c94f99,0x14db8840b2011eb41b47,0x69be4b1c7c1b01cebf02),(0xc7389bc22cc3b171a7db,0xb1f9504f8fd48094c300,0x87f20965cf750342bbad,0xef491246e13685de3e3b,0xeedbc598943fafc8eef2,0xeed6851faced97ab13e4,0x47ef4bf3a1ff9d46d3fb,0x7837b4bc4fe8de85825f),(0x7cb964fb09de89f3e84b,0x496e217e43c34e35c310,0x16157120c9c3fc7faf50,0x4b2b657a7470d0b70857,0xa3c1dc2854c957472928,0x7110021f067a422fbd12,0x443d4fe299f872fd71d1,0x3edc177f83c4d58e3b8d),(0x8f2235a9ec3fa5f2b40a,0x1a8699fc73a0d49797b2,0x5351ccb897601cbbb4d6,0xf0e1af6b55b1481bad5c,0x3b26252bd2d63246111d,0xe5237638113b5d5e753d,0x1a04f1cd010ddd05ae25,0xa62a168a091b7beaa2c8)),
((0x6f58c68800ecc69c9285,0x30422fe3337e123f8a89,0xc7a923092d30587bdd0a,0xc5d767f9b5600fb67c7e,0x6c80884bc9533cad22f,0xfda3e2dab1eefbbb00ff,0x2f36d5ed5e7abcaca1aa,0x5422237038b991e410a),(0xb543faeaa676191d5156,0xaa371ea20a7195bf8055,0x39b535292126a89499d5,0x41ab09819d003dbcd26a,0xf91bd7e84ea65fbdc1b2,0xff290126e656aa97e7bd,0xc889f1b62752ba558c,0x641ef9bcd9f33bfbb2d),(0x8456939a5ddf1d1d138d,0x3c0e55a135f9ad091e1e,0x713e64f3d72f3934054,0x8c152c6564dbfbe787af,0x2e2babb11891406c9de4,0x53028a049565c412bca0,0x6555d4ec49258758f414,0xa722875eb30f48e9a67a),(0xa6f0856ff5c33432543,0xb49e1925da58c7859c72,0xa90521b8af3057111ae,0x560c6a7db5097b743f61,0x60f22fe47680a0e6764a,0x74e0060205e7698c0356,0x56eaf96b52522c67ee18,0xce9330b12ad251cb2986),(0xc4c4787d03c66dc4381e,0x5e123fcecf5b697cdf76,0xcc97ee9170294209915d,0x6d7a850eaafde504dd4c,0xff09ed66fc066a355581,0xb7ff029069e0c52118dd,0xb3241ec91a0271b7cd3f,0xe75f8cfa6c93536f3e67),(0x21ebf3f5c8da52996358,0x1833fefdb03b0a7993,0x3e1f9a757fc37ced9083,0xb404c4dc934034d9f3a5,0x1c796dc04f87bd9a8429,0x3a2a51db03785a6b9bba,0xdb7803117f2a720a4f50,0x953158e911c579f519c0),(0xed7646ebc516c5c39823,0xf4197dac31954d4bcb44,0x8533cfdf1a253289869c,0xfbd70f3377ac7d2330f7,0x1397518382047fbb986c,0x25fc5f029ca9a34b69b1,0x94100e5a7a98ae129528,0xc0beacd62f4afa28c247),(0xb91c649335f365fcfcf6,0xaa700e4774d0fb9b0282,0x61bc674e8272e299c034,0x6f19bc1ebc802d01e28e,0x44d4726e9aeba536f1b5,0x3cf24f9730bd981d6a08,0xea98c820b4257a1f3286,0x57e67ab1ea6c1dcde9ea)),
((0xf88ec2d1c976a00a466,0x5c9d4e02b5cbd2fcc732,0xd6cbab97c7fb3f633712,0xe5c4d801a59883ea5ed7,0x16bd38dc8357679e5d20,0x63c3bf60315fdf83302a,0xe315b3df9c26fa824a95,0xc18d0fa02a17a1118f6b),(0x84d9ad89ba845929ff0e,0xaaf16a54a7b63d0e5b0,0xb73e2265598c9e56c618,0x9a5b1535ea25c078a8b1,0x5a4eae4aee4a5f164b2c,0xc478bb30ec448781f3f,0x84f01c6e50360f97e48a,0x27c4da52caa5d000eaaa),(0x943f7b6d2d32756828e6,0xe42a75bb1b24a38b6d5,0x4c3e8d3085526094ca90,0x2277c48f3eccd30cff9c,0xf956b1f00ebc73d8cf50,0xcb101e6fa25f79b50705,0xa4ee830b3a0ad20d9150,0x1db76b2989ee3c13a1ab),(0x252cdff5240373bd3127,0x90f01e879cc142c868c4,0xc00991b161a5830a109b,0xef36096d4c4bdbcd93e,0x4e378c575da7cc84f34b,0xb2ecad66618ca7b6eb73,0xba16b547690059a0b1d1,0x6cf1b878346d8b45568),(0x6ee3c23b4142d38bf247,0x8e4d475db216fa5a011,0x83255995ee06c4be0794,0x4f94342fdbc321ecb3fd,0xbe7e733d4610af144b42,0x805999716b340a6c3853,0x4c77ecabdc820a2e1d84,0x543e7d2b2504b7296bdf),(0x51bacf1ee53eb6f0a33a,0xe94fb59686425e8b3b93,0xc64775e6a5108c4e973,0xa1982f60ec1cb88acd9a,0xf87deaeffa8d6a023037,0xd9fe957ef3c8ac2a702c,0x2416081add4526a6ac8f,0xc42b90f902c5937e6ab2),(0xab21590bf9c34e4d1eed,0x20bcb016f274d786b1cd,0xf37d9f1351f062a1a913,0x4860c2ce2fbcb240c60c,0x38bf612c706cd34ec388,0x13ab3da12a6bc96ad3b6,0xe177e82c7802fa46a770,0x819f4571542f47bec537),(0x1fdd3fc528d8648db9cb,0xde9fc33dcaa1ff6bd6d4,0x6d7869a6bacb10c9fd26,0x613f3a44a25f116ae765,0x87011a91dbcf71ddf3e1,0x7321c649fa824fa7a2ce,0x24c6f470cdc92493a703,0x6a0bef5b2ad0d1e7a5bd)),
((0xe832e5c8ce86f1804274,0x81eafbd72e5d7a8f9d1f,0x12bedbb775753a9c870f,0xadfa85653f32c1580b57,0x7cf35e8e1d1acc6a480d,0x53ffc0e60d12849a4049,0xccd1f5387f390d7eea0e,0x6f532acef2778d2b33b3),(0xa2b558f51ed43ee4c7,0x2348a3df9ec6d3f363be,0xddd1989020bbb6ec7d4f,0x6b8d0bfd3eb1d10051da,0x9220e94db50a4c19cf15,0xdd6ce1c03cd0d35a9f32,0xc726fa7ece7f70654bb1,0x9bf9b9e1b9d2c35c8fb0),(0x5dcd40a937a28501a89f,0x286b6aa74c26041ec046,0x7f75acd0bb7f1ffcdc72,0x2036327c36d291364a26,0xe769e5edfe0582a31385,0x5c04c85259c0e04a5193,0xbf25342310ba50371c31,0x7165422d539b169d8ea6),(0x44e8187786503ee739cf,0x9fbaa1bca34116be8e79,0x77bb56318e1cc416bc5b,0x5bb3edc5e0d6471c981c,0x3f8eb08086feae349f86,0x5bec492d2facc398f33d,0x34e12bc00aa804b914b3,0x61a98e0717ae7c8d3789),(0x4f3fd666f01a643f3d95,0x3f4fcae1bfbcb1540ac1,0x3a32f3ba721baf69b712,0x5c4bf4f2d9f7057cc7a1,0x806dabde4cf1c4720a3d,0x797ca44e8d038b108155,0xf48f03727c319e75bca3,0x69efc684428e0a3642dd),(0xf973b400d1e9ab679d91,0xd660207bc55f883f6e32,0x4c35ab97fa77f4e28064,0xe54a876fa3af19556149,0xe2733a1920c8adfe1004,0x9f678b28aee398440b8c,0xdd4a89bc52b6569df429,0xb3ca6f8e314eacfd4fca),(0xa58cf33da43bd030f643,0xdab1a14b6dacbb3667f6,0xb209607f3a0e1cb50f37,0x1068f8011b894d631c8d,0xe0639a47c115e82440fc,0xad4277da762941aa671d,0x2b8ab996b483e60d6b51,0xbb95a3715c8f59289b85),(0xc52cbac683c38c0bedfb,0x2550ff4ef2585e0539e6,0x47e8f7878a80de28a09c,0x5a32da4d12da43f70a0,0xedc4450dd7715b677bd3,0x3bdc1f92677ec23601de,0xb7d48adf65f0e3f1ca70,0x72f5ecc04ea542ba2484)),
((0x4e2b98a4dd830576d7ce,0x3047c783ea41c383c0ca,0xeade8be9c8e4f89d38a6,0x163fe8231f80e9f81f22,0x834e28bd9b5b462b477a,0xee2a37a45a56551dbf83,0xeaa1898745a1bda71372,0xcf093411eedd8eba2968),(0x87abbab5ddec9805ed8,0xe8febd69e18125cd4eee,0xbae71876aa977cfe81ca,0xbc027d2047e765624f,0xc6bb578cc2964864b3d2,0x9df87019df76026d50f7,0x69d9c5628ee14b8467dd,0xabb06c0cfa735a8b0917),(0x4e33a042b46db4d71af4,0xd2fe1bf003c71c2e0ab4,0xf513ee274e9c741d9517,0xb078175e52ccc0231ae5,0x81d08932edb0a103d67a,0x71136fc24700c7b6ce9d,0x709c3086d60607164a10,0xb51fcac9def0e4a497a4),(0xe329eedcf275fc1b1cec,0xd84237888067e916266a,0x73bf20f6280b370c5a7f,0x7ad83c633769cfc2fe16,0x87699d3361dbd7703e2a,0xa87fe293c6dc2ef391de,0xa5c8c95d01bf83c61f1c,0xd40493bbfd58e3721570),(0xe8d254af74db8c4d5766,0x1259f5f705197fc5d787,0xe6301087bb5076c3e585,0x250771854f57f9a624ec,0x6cea07ebaf253a163965,0x61e381fb50ab1e799523,0x9fd321d40bc5bfdac1c4,0x17681606b4c77e80a5d2),(0xe57151cd41392c25da7a,0xffc33bbe972b8d7ee761,0x93698e74a95e2e4828dd,0xe166a0e4caad092181cf,0x8c7fb33a6b721dd8ccf9,0x5f929d8ce0c6f5a31711,0x25923a171768e9158289,0x4b956d13a8109f3d7156),(0xb35646b14f16d320f3e7,0x64d81ce4f1ada2c8049c,0x3350b1747a0c3b24135e,0x6597142ac2bbc07370f0,0xdcd3a0f14c2875bd80f3,0xbf3514e31147feb4e0f9,0xbf8b9fdf53aad731a01c,0x8b07831f74c160a1768c),(0x79ca2c641e73eaec6970,0xa29481397c1fafa0c0a5,0xe32e93aefcdbe484a270,0x3737730f169a064158f1,0x19cef2c32172ee79f3fc,0x34643354e2c9e74bf2c4,0x5db1d366a6797e58e704,0x70d997bc9cef038036e1)),
((0xb61d75065b08d650fa53,0x5a0351a863623a2b177c,0xb2758f0c43c4616850c1,0x5244e98f550ed39f20f3,0xcca0284435d735655ed,0xe9a31db980e9192d4cd7,0x77d829e69c906f82522e,0x40a11fbe8429b79e08dd),(0xa02b02d1eeaafa7030dc,0x1890e894256d7828f2a5,0x9675177528490d868c01,0x66b6697e5660a74424c6,0xe2ed904be6ea79a51b14,0xbaf7044ce9670ce369e4,0xfd0b61fda8cc40485dad,0x8e555b3cd135627e43fa),(0xe0650cafd429d4b9e680,0x80946bcfc3e10ed93494,0xedef146e99b32d665a38,0x78dcfcca8969b1c77816,0xf5ba285a61ff0c6c7a9c,0x96c25400996a1f584f38,0x1a883b5e3d051789146f,0xdeb4381bfd8df2ca81dd),(0x3c653c42a7459b0c2110,0x581e03048117960c8615,0xe26a871f262d3d409902,0xbb2bd4bf53e1af80edc1,0x43ad56024624b907d82a,0x968f8f4108554fd6294b,0xfdc23ba55803619920ac,0x55e8a56862e8e29b990f),(0xbb504bc04867231dc623,0x88853ec104f2f6ad2205,0xe1bd2541af31e5930618,0x713fe124e74defc9f985,0x9118e00e70f5ddf9cc94,0x544b58071c98fd5cbb9a,0xb3d6880c47776cb5e696,0x5e7def57ae33ef78aec7),(0x8aa002a66b3727815f67,0x43519df5223c9fc00839,0x2c9aa25b10c4a2d34422,0x7ee755bf7542a834db2,0x66f9619ee0165e7d6c6c,0xe04fa9ff68a74b9d11fe,0x30d2375a60e36b5684af,0xa50af1f517248a7199a),(0xb277a60999a56e68a752,0x957c38758ea717f3370,0x9b3b2e0bb9063f125894,0x28facfd78d8dd7af1f6c,0x8b8b509a9f3d00a098f1,0x871a2e3ac8200755bf05,0x8739cf98ec8813a51c00,0xf6796bc12ef28b6a137e),(0xd3c3114354115d7ee553,0xb9464759019619290699,0x1c3ac82007d2cbf572fe,0x33682e41f640ce166084,0x16419b15148e114ba4fd,0x9ec5d1174cd0dab582e7,0x3c6b5a0e97c2871ab610,0x453d50eb8ecff5fbf57c)),
((0xa1df10a4e3e5cee1a01,0x30187ca3c698ebf4f695,0xdaeb905bdfda0be2f72,0xd80fcf33550694e22837,0x9183dc790e98a2fa16ef,0x24a10b4a3837f4631116,0xad8a4133e2a7b557cef6,0xb14eec297b4f323bf180),(0xb3ccecdac72e73a4146e,0x829b04e0ccccf6ed1584,0x6a0fdecdebeae5290af0,0x8bd1a749ffb6e91a45d3,0x382b6b4ed55fa766da87,0x96179305c7cc71a160a5,0x4e07edc53bbae82641db,0xf790dd9306e739b9d060),(0xf96fabdf49ba5c56869f,0xf8405b773ed1c8d8b938,0x322ba565bb3b00913785,0x3fade95f00ec7bd211fc,0xe1e00305a9dcde5aa091,0xe0e6757c67605a44341c,0xb267d4eaa2fd0e29107c,0xe2294756eba6b2fee8b9),(0xc774c4b0c6a08a8e2856,0xe3c199fee8d77b971083,0xb4f3b846ddb23dde7ba4,0xe466d2dc704e78754760,0x8a4ddf55d9b69deab243,0x5e1faba21dcef2770ad2,0x8bdfda562091de4159fe,0xf7617edd5cf408ce9604),(0x2a6b94216e7d29e56258,0xd0ee78c9dbffc071b245,0xdff948c60be6ba42c5b0,0x5d758517b96512315e1a,0x692e9581e627fee9573a,0x9cd1a76c41b5aa80f604,0xf9f0e259e6d43b2e231d,0x30eb784b2f7bc9070081),(0x6d2367a3eaef81271810,0xbccd4cbee40571743d21,0x79198d398d6b93e30000,0xe163b8a1bafb77ab4c34,0xad9cf52328403958b657,0xb2514c9fdbf308a21320,0x4834a1bf917617830532,0xb1ec590fee9e4e9cf3b6),(0xd8722dcae68757074158,0xb3ba9c5b8a74ab36d6a2,0xe7d1700d1487f36e16a1,0x4e0a570698370c8a58,0x948b1969179c3814514d,0x8abcbae8ff6d01d819c1,0x8acbd300accb658cf1cd,0xb4868e565c4f1e21a478),(0x3177082feb94f60c1c8a,0x2c9b193e50a6bb7cfe35,0x169ee7d2521698c8fe0e,0xb21aca708b65a34bdfce,0x808d9118cb2cdd851fa9,0xfdd34fc8d50685b77e32,0x8c03b48a03cb51f3f20a,0x66fff6afebb066bc437d)),
((0x4e0c03acaac1bb6aad76,0xbaf2abe85e6de2ddfc1d,0xeada287ea8feac416070,0x85a26df774b3af1b24f5,0x744dbb1e11c0562e796a,0x40a34b21c6363af08960,0x8c19b4210ac02e52a2a7,0xa29377da98039ba4bee7),(0x78695cefb3a01457a9bb,0xb06c0fcc6f1f32096e84,0xdca70c9c1323651cb750,0x30362b31414b2452c5c,0xe312aaacd4175eb49dde,0x3515a367787fe2a28040,0xc006bec34101e8ff1c7b,0xc26eb1111e239f82e956),(0x92520c3dfd30a2cb3eca,0x6b8900b678818de02d6b,0xbed20b63d2ca341963fa,0xf2d80e133150e4f727a2,0xeafd5e3c5e28994a7ce5,0xf3d6d404519fdbd23a73,0x552287eeba8e05b6f006,0x5e9be7bd769981c00c1),(0xc5ad7a7e03f41200bd3d,0x190dc9198bae0ec4f60,0x41634d97c74c01fb189b,0x144e69d4b0b34a3cdc5b,0x5deaf798c02eb5065ec4,0xc9eba6e8d970ec69235,0xeb4ff1463ad9d9be9b33,0xa3e807913b8d814e459e),(0xc841fdf3e4c5e40062f2,0xc914fd8e8d00dd80caa1,0x1fb09978035ad968c3ec,0xac0754dac6dd8ae65f22,0xe878812d47a7510d41d9,0x5bcb57bc8cdff340837e,0xfe724aa65b7f75660266,0x2783f15f843c96bf8e28),(0x4053e61a8bc410318993,0x4d7652e99252f902b597,0x9a52eeb35ab71eec59d6,0xb2ff31849ed7ff76b198,0x7d97620727ddca02756e,0x92fc2bac2973abd71645,0x413941122b2bbfab40c8,0x305d3dacdaf49867d870),(0x30825b2569efb460836,0x98385feaf7d32b751a87,0xb363afaadf11bcdd3358,0x6c37e6acf08191932889,0xb823b52908474c20754b,0xad3af9df9c0b2bb4e417,0xcb95c3a54787197f0616,0x47a71ee20538a88653d5),(0xf47070a8ef9c6a050938,0xffd7ffb7a85e63bdeb64,0xd25898cf03c1667f4385,0xe2ba9fb91dbfde78fd2d,0x70a6a7322a793107fae9,0xbd45f4491fe1f32cff0a,0x6af438c9e8a5f551b59d,0x23cc37fa79515ce88090)))

def page18 : WordPage :=
(((0xf5688b43e246895c6e4,0x3a2ac587f8386f8b8bbc,0x47ef9568ed4036da0365,0xc4bf1d4040ef6b177500,0xba01783a5ca007e0d937,0xd0d831e19d76b079d284,0xb25859009de4a9006d17,0x32d1ae9b7839a8141472),(0xb5fbd0f7b0a7a513d103,0x398c32793f6297141592,0xe44fc964275dcd8dfc35,0x731c42ca7ab23f52e1c3,0x29fbff7be16731c2c468,0xceb51d05e78cbf728f7c,0xd8235ad7fc1e00ec61c3,0x51b393321721843870ed),(0x90a5fca841d64129366c,0xafe7716e58f6dd2e25a4,0xa7d6e784d4baae21fbac,0x51d5a40e3621efb6d163,0xbbbe501a39d7c36cb5e4,0xe7dee430bc5b3b4a35c3,0x922a04676cd5ee07e643,0xbad72a721b68e42a0eb7),(0x1c358abfb987b8da5f5c,0x7bb2dba65c7c81d9bab0,0xeb893bf809378d031ea7,0xa2cd834fc62a5f5d755c,0x98124a33f5edbb348d8,0x8594fcfef303aabad9bf,0x159e7beff89c728cf626,0x3af14781c9df78fc3fd1),(0x66818385c9bb68d08502,0xfea9e851e07e020d828a,0x96890cc07b1abc840cf6,0xf11d0f84c4b5f5d5a13a,0xc8175c0605f46f94b399,0x59009eeaf20d722d7db,0xbd1cc11cca9072d82f4d,0xebe3fd149be20423f85f),(0x1c423f568929d4943c03,0xafcfa873f15d0f909beb,0x4e3172ecd32ac2ce1bd6,0xe169a4a1e77d75d1d403,0x99dabbb4763b9f94d752,0x4695604482e53b397193,0x29e1ea9c303374261344,0x8b367306854261a5abc5),(0xfff7931f797d1670321a,0x96600b39ee82c8628891,0xc96a547b22d8ef7a81a,0xd5d351386c129dc1f269,0xe41e58e18300ab26f21c,0x1cebbff91c6c50b37fb0,0xb778297416eeac84c6f2,0x637340ece1c2504fc966),(0x6898fa054d05d7a66837,0x78b1151a35ab99699736,0x75d285a4bf57232f87cd,0xd4aa0112a1a915ffdc8d,0x2328bad1c3fcafc4354e,0x74c320bbd02b1f1a4559,0x4cae1fbf57e930efae72,0x7dcfe2db41d0cf4b58e)),
((0x6b423c0fe471371e7aed,0x13527724cc1fce5ace90,0xdecac4b2cc236da19a15,0x5db0f8c82e359e840c64,0x947d682c01b5ae3c07b2,0xce1d9644ef32df417d34,0x47347085fc49012153a7,0x7480a36d68b6c6356555),(0x37a6826e342a8993af27,0xd9d8f5053e3218974873,0xf85d87d3ee77abddca85,0x9c8a21badf62cd5053dd,0x851c6d36b52be31fdc28,0x7e94bf6cb179fda49f25,0xbb8096b4e7295cde53dd,0xae67e5db8d41828cc1),(0xc07dda6f5c06fb7dce64,0x2dc8714efc1bf2795b1c,0xee48bfae093be00e150,0xec3b8024db0ea0a86502,0xc901264bba915a74c409,0x1d9644ef32c398df79ff,0x65cce0914e288298a7ce,0x283c7f8b04a7fda77784),(0x73fc9b907d47a63d9d89,0x48e778bf61969e9b76d7,0xb7624d25d0a2c3cae9b4,0x5e62af333f3645692163,0x2af99293b31fe1281c8a,0x5edeb82b5e9f8dc55bf1,0xaf5029a92840f8e8ef73,0x796867d0c3b2478decc0),(0xd00f9e5e621d78375efc,0x82078882c07b7b4af969,0x41de800a9c64bb3d5307,0xac132971af51bf025321,0x43a817c5f2cc6fcd8e0f,0xd75879db084cb75e1cbc,0xa6654ce560da7f2b2505,0x49143b0d4415f01c6e50),(0x9ef61dee0d77b4d9fbb0,0x5b91167067e87fee7487,0x82d73709bad6414fe14a,0x66df7bf9405470e6b7ff,0x32e5f077c085b0feedb8,0x8a1026c9057ee5342413,0x1f4b0669b5f2d5ec9bc8,0x189e284834e933ca300a),(0xf1d1348e1ed2ae525716,0x4478b5cd8121e044376f,0x35aaab34e960289f4df8,0xb706e3ab89cc9f0e5e04,0x25259b16e79dbee1a57c,0x64cb221e512aa28dd61,0x7628c3569eaf348493ac,0xc39eba129770477903f),(0xb3f4ca2263b211e160e8,0xe57717ffb17c1f8cb60f,0x1101bc33a96c8baae9fb,0x7ebddbb45044936cf270,0xce07cbeda6356543489,0xcd1e5cbe60f2e8719a0,0x58a0e2968bcf35af2e6b,0xeac635d8d9e330538b0)),
((0x273496fc68ebe9f007c4,0x3b7a05b3b2d289074d1d,0x1e55facbfe347a427cda,0x3d64935ac5b5b514fa5f,0x895f8212b3377615112a,0xab7882548303837097cb,0x839048ff66ab562814df,0xb9cacf7bffb4786c66ee),(0x896fec94ad504edc7fc2,0x985e0e71f2e13eb0261c,0xc22b92d89db17b74d474,0xaa3775c4c9dcd693b269,0x7cbc1b0d7b53068fd2c3,0x4cc4b31b6422c7b3be73,0xc776debd3f4280ee52b2,0xb1a599c55a189d1d74f1),(0xe82510f2fcc48ff6b50e,0xc0ff48f87464d1de1d6c,0xbd1f71aeaa5da85f4430,0xfdc740ca6e5f9902903b,0x271e8f931b4fa1a2e85f,0xbfe3274577a518be64c,0x9aea01c59699137c0f28,0x6198b42b200ee08577eb),(0xb57ddea668e5c537e749,0xca5b7d6dbfb79fa8ce60,0xfe1763758be0b9ec6100,0x5a7dca1a9fbcb99316b1,0x835d2008b9e739701109,0xc850b3c6981c32fc64c,0xdbd0047754c573bddc18,0x29d514be25fbf162d2b7),(0xe18ff2b7ab80481f2f1d,0x29c51f5b81277bcce7c8,0xd2bb9bb8ac3a4ac51254,0x14147e2cf8aa34fe0830,0x9725fa3930c58c361301,0xcfb37d4cc59299cd58c,0x42782fe961b867259bf5,0x807f5ce3f4d12c9331cf),(0xb74dfcf407f42cda6a87,0x693c0b1aaf2b6817b16,0xa1ea89af8eac8539745e,0xe7662a236d0820f96097,0x57cbc1cc535bf81b8d69,0x83b3757e28c13e09bab7,0x3f7fea079881849ef9b,0x8c600a69d13aa7df7ff7),(0xa3d2eec3a0c8b4d73eeb,0x936ff69b458d4f897de9,0x71c7d450254d9420f628,0xb8c920d8e79cd2b02f4b,0x75ce4ea7f6b0f5d3453a,0x316d1724845c51a71db1,0xa4d1bc61bfaaf535e05b,0xa2bc0b67cefb3f387af3),(0x4cbf5e73754358be117,0xf7832a183e2eb1c16c55,0xbb5c9d53941a22222b80,0x62eac10321b49d1b1785,0xef4cc8138d82fdf0c249,0x483246b830b5dc2c5c55,0x243338c61715830d0bdb,0x307f127a11aed52b3b64)),
((0x3629824a9e312e6e4eb9,0xad20646fed9d3fea2ed1,0x96290a44b769cbed2185,0x1352aa136f7029396c7b,0x6b4b8651d0d64bb99c04,0x9d497d964e55a0549321,0x33be57d64fb698f9ad75,0xc103824c08ae97bf7396),(0xbaf99a25415bbe40c770,0x9e39ee303764c00fb6d7,0xfa5e7c41386affed4dc5,0x18db22139002ba263f1c,0xee4a5a7e2492789b3e7e,0xc4027c55e12bc0006a17,0x8f1105813923294ec715,0xa2a8aae2a002cfefc6f6),(0xc8b19061fe3ad3edb7a,0xa4adf7ad77747e9b1668,0x92bed8e9077dfd207d27,0x65aa4a82ac5d33ea00e5,0x62e7c5dbf7329909425b,0x5d1d9ab2b3e44e0980,0xcdda7cc378c51a245385,0xf481fdba5271add81b5b),(0x9467b0c39e3465870fe9,0xc62b2c0f3e446324e293,0xc68365d4aed48530a9bd,0x10d6408b5fe9eff09d14,0x4571b2e8a8ebc73b6882,0x748ace46a80a3e13640c,0x96cc6e3267793425b335,0xa1fb98f16d837e946d86),(0x1a6aa2c2b1ce2c26611e,0x3f24ac0d957c34d6960e,0x200760a77bc10a075667,0xda15d0b6b67845915055,0x6ac212951cc1ba489367,0x7e3d3626fa0a7faaf063,0xd57830d486231a86de29,0xf2494edc03e1b3a0794d),(0xf4734b6e9b70c09a11fc,0x1e89a289884400188ed0,0x830e9ed91146432be1be,0x2aac475e151057885cbd,0x41140eb20b28925a42e7,0x907c23241a80058eb9a5,0xeb1f85e33f37c826d0f9,0x1a1f38b89f00d293071b),(0x2d63770a1735906dcfa8,0xf4b16b96fd6654a7cb50,0x5489c3f81314bc48f625,0x362946dd55032ed2b71b,0xc5ccff5a0e92df9002e3,0x80204df203266f89211d,0x4813ab11049090c4b355,0xeff41b8b16e96312eadc),(0xcc06548aedcfffde1d4e,0xfa91f7be612003e9a63c,0x1827a4f3f8adbe974470,0x8cd698c2001be62febd6,0x1d7f08176e34e9e7209e,0x74f3fd2fc0025beeee42,0x77077e3b77f77e026eb9,0x80340ff90eecd3ce6dba)),
((0x8b388d00b4c70edc85ff,0xc4ae41886c81b95c979a,0x49bf00f1054d7260a107,0x7e09a0b55a078e968e27,0xc0f07d02672e12db0d31,0x6e63bef921f53d42a6c6,0xe748c7045306e774ad87,0x8125b33d1f0ab0878b6a),(0xe89d8f468e7d8b1b7634,0xc3b728bdecce36fe95db,0x3cfa930c88404c533cb3,0x88ef0674aeb9d992020,0x76a88b8eb011ecb73a15,0x9b8cebd576e913929d82,0x1d31658a6743b19e41d7,0x4581195189531a77189b),(0x9eda6a835985925d4f52,0xab0144fe732edb713188,0x25be2c4512d1af958678,0x59f7ab0cb1fe378c09ed,0x18f7ea883d933cc703dc,0xdb8c42c553adc1f23c29,0xce5fdd44fe89b763ea90,0x1a74763ca0c06ae92543),(0x828ee73f036dc15384ff,0x8ebbba14b080b8b3e958,0xddc5e37b28ebc55d784f,0x9d0cad9a65ce29189b7c,0xaf872eabbc5c9d7b339f,0x85604352ad8604e3154f,0xad77f7be91bd041c71c0,0xbd6f545a310e94d4c0a8),(0x5039a33fe512aa31806d,0x61378028060777c1edc8,0x58089ef02f2ed9e64bc9,0x7ead0c71751524b66037,0xeb7f839e2721fd1df21c,0xf8dcbc0895c87708b886,0x235d9a89efef83cce97,0x62bb29ea04554a879444),(0x9f600bc4f5748545e470,0xe7615f7d96e618a487da,0xe119c365c567dd8f4d9a,0x641743613c5829cc0820,0xd77b1e68d2ed282d9cbb,0xf4f0943dfa3336f27bcb,0xd7995f3f03fd40bd6e59,0x1e7dfa63c051149da6c9),(0x804b005ef105537deca0,0x3a82e06d1de9508870a3,0xdffcd54a8cda1c52103d,0x63caa498c04a6ab2364d,0xb762e7104123d52b4c30,0xd98cdba188efbc273ad9,0x9f2d611aaa4fa68463f3,0xc19e5709b08424393394),(0x151336c9853c580d8fa7,0x7461470b0356b3d28ed1,0xf9c5d979048a9d8f5045,0x33dac58d6314fc22ba95,0x4623dcd2c365e7a195bb,0xec70273e6a1e7af149de,0xb40a28e96bf6f1acbd31,0x64c68960f05cc515dafb)),
((0xa4513eb27523e2f2c431,0xba54ded4345b8071aa1,0xf76ce57f58c511781850,0x44f01a0adcd97d25ec88,0x5e57e847a4b7e948886,0xbfe0328b6e412705d6f3,0x6aab7b3fb3150454bf2f,0x62a45af1eae83fa192a9),(0x685ea76fa55bc7d5e19a,0x7dcf2e0ff4fddd483ff8,0xebd4473ea3cfe320eb42,0xed7de4492c5d528d846f,0xafca69b47a29db481de6,0x823605b6a89a3ba05fd4,0x24f8aab42672319027a0,0x98d859fbb6d3d5a136f1),(0xb27b3fba7d218ed04566,0xadab5d73eaae3dbba9b8,0xd9031be49b69bf53d02f,0x17c47b1507dad4c3335b,0xfe59858e28c40e769ff,0x63c4cd10fffccd23e39a,0xc4f34175581cf908ae2a,0xf122c1b42f14b8be32d),(0x59d91bf1bdf903ced9b0,0xcaaa3cc990a03ce8318a,0x40594f2b497408552c35,0xcae0894dda585c7237d9,0xd50ddcae20f2a3d2d85f,0x180e713138e3eb97672b,0xfb35dd62f2719c3a8e13,0xc1f099acfdf10ebffc86),(0xf8b3e3d24b2fe2ec189f,0xfdacd124a789015cd63c,0xe35cb5ef54ca0a6709d7,0x5d4f5cfdb92e2f9d7db7,0xd28a9906075b6a3a6ab8,0x3c5510d5fc2df231d394,0x4fe18e7b39a007f22ad,0x5b26eb31b01832ec0238),(0x975fcd476d9a45c6c291,0x6daa6a5703f79f090990,0x60138ddeab73ea409ae5,0x51ea33bbd9e80c7b8c6e,0x7426ef8fd9a0c3ec0621,0xbde384423a67089ac114,0x1381a87eff44db13cbe9,0x4267f2086cc93f5f2a83),(0x92ddcc11922775af10b8,0xc92d83d8df5c91900b66,0x2f11e9b72dc04dc96558,0xda89b5235791ff000343,0x8d61ecf8c7f625d4f710,0x1f27d0dd2a815fd13659,0xb5105e263b4e6c3d3dfe,0xc003c4e079cf403fc018),(0x66e24f8f923e324b38,0xdc1c5e83250927b25a9e,0xd58c8c38c335d28691a1,0xa01fb2990c69a3bba3ae,0xeaefa68944666907d9dd,0xc0928f7095da579f22a7,0x5133571e4209ed1b7e50,0x3a746045ca236fd1c2fb)),
((0x69210860ba77850bf81e,0xf0881fc1d1f77feba8f2,0xa3dc9d1ba5287f5c960c,0x8618c2aacd478e13998e,0xaf78bb5d5477cc82b73f,0xcc1c4f3c0c54fd7adf73,0xd570a0651c3d4b0921e9,0xe49c9801b3cfd4edab06),(0xd8f093bea1f1797a7de4,0xf51383befebc0d02634f,0xb091d968cb269d984f20,0xa29818127b60414bd47d,0x8a09f45fe83fb7cb6cdb,0x4fe41c07ac8d21fd3948,0x1ada9fea3cb8b7152fd9,0x8d4314411a7a638a1343),(0x406e17f38f6effeea843,0xd297fdfd966aa2f5afdb,0xad90c3c02f895e74e013,0x78d540ee06c5dbe5e479,0x39a6c78a800ebfff098f,0x638c019f89d30f5306aa,0xe0de92cf041cc5b3d71a,0x3fd5212e63fb2f234215),(0x3746e648e9b9f7ddc746,0x9c330f5ce9ea2ed96e64,0x42d65271d99b3374f301,0x80c56134f9cebda73a96,0xbc77d7c9bb391f88570d,0xeba3f2b82cb2356bb4da,0x632da68660777b7ea8fc,0x94c73b302a47cdb65120),(0xcd0721e7dd7591b07932,0xa314c8ab2a8534df7eff,0x687416a482e84dc1e02f,0xf6807cd88423d0558088,0x6b66c8818b51cae748e1,0xc5b6c862165f34be9bce,0xbfbfcebaab37cc608dd5,0x95d5524cbbe87966cc1d),(0x8c2726089b3532de0d74,0x113c11d078a1c188e326,0xa4189bbc052a10ead0b,0xe746b377bf4648a1f5a1,0xab55d030bc432e9676fd,0x7ed47fe5a031543e78a3,0x4c67b3de70da5dc3b81,0x28fcf6490c1be18cd826),(0xc47dae1191cf1c87ee31,0x2d3ae414c700856442da,0x6e12d75f8ffcd226e3ee,0x111c223947d98aa3ea7d,0x3c38ccd3eefc871e5850,0x31362a555d80c1d5ce9b,0xd1a251a57c76cf092951,0xe85497f27ee39ac08cf),(0xbf3ff821b3602b31f50d,0x8d237694ca57829b43ae,0x4edcc421f4b6b7ba1361,0x9b419839d90b5cc77b79,0x224a23bd67f9d8c0d76a,0x63fb7f9d19fee6262901,0xbd20320ab3b2470067c2,0x24b1585494e7e00a5832)),
((0x5ec024815d430880a9ad,0xd3bc613f54583b1b41cb,0xb323f24e8943ba1c3d7e,0x532a696aa14b4b04f3fe,0x5e01a18121799ea410ee,0xe8b275d8b10457520ec7,0x87927ea0c499666fda82,0x9967142efc003e92249a),(0x6c41ef4527942bcd079e,0xb2f2411968977c3d371f,0x59908f2f7b22e486eecc,0xc970d78a98915a3a8a99,0x27ec71731e0002a42e94,0xd1f4c320f6e4cb17b30a,0xc35178533226788d5e4d,0xefbb901489c623fbd13f),(0x90159c7fe5483f417cc5,0xe07090d29ca609e7369d,0x5154eb89c934f01a9f69,0x84f977b2ab2123891651,0x6d7961e4f95f6e7a96aa,0x8f38d6cb817cd91e0e67,0x437c1b3b8a33a535cde5,0xfeb68dc6dd6d1728f084),(0x93d83a137a24a5dd5d9b,0xfe68a638b8c8875fa281,0x781238cdb23f504a8c9,0xd9b63a9c4cf6bd655c,0x9ff136c864db32a2e8b4,0x78b1c3eada1da99f0b4c,0x2a9e9c67ab827a07a30e,0xc0c69ce143cbad745f32),(0x675a491639c36c93f003,0x667f3a8f771659042e88,0xa005b7bacef85d7a8659,0x370b4ef274b45b78357d,0x43bdb863cc6b1f4ca23a,0xc8b2b80f8274068b9c2d,0x3fdc0dd084e192e3da7b,0xdf10a5f37c81137395af),(0x7d808a1904c27982e4c7,0xf5a8d59bc371db88e058,0xd2607f35ee3b50a83837,0x96018899379312850be3,0xef64f1798b0c25819229,0xf950dc46b1a95eb85a45,0x8f88aa6b9d29a3099b7e,0xf814a1fa06e54ece13be),(0xa726fd28d308630ef709,0xa272905b7e3fdf37c1bc,0x32d51d33cb7877ce1408,0x3057101fe4e2ab666330,0xf1b2411197dff9d0840c,0x48d626f1f3edc7412118,0x4d68060cf6ca6870988f,0xd00a1332434cd2e9c4d),(0x92f60907defa87a3bcd9,0xd4ef3d053d048d105413,0x75bfaa749f4094fb493a,0x59a11f841dbf2a520caf,0x52bb298d545ef8051318,0xdbd20527ced35d712d24,0xc0f19f5508b852579b4f,0xde2dd45be90cf413e6aa)))

def page19 : WordPage :=
(((0x5dfd6e5d7682187e0cfa,0xd22303fd3bad9d15df18,0xd267773b27708145b403,0x5af103e30eb17eea928e,0xc256ad4d4f062cc70329,0x563f98038c5cc29431f2,0x19d8289cd9592890fdb4,0xa577461a32a11aea07af),(0xfa991fdd8f13bac853fd,0x9babac6470f7425759f3,0x5657cf2ba5047b833caa,0xe26e91fa04deb1850308,0x50deef0675af461d9ff3,0x197b129dba65819dd965,0xe40195b04f33f24e7501,0x7687a991184b02b5c45f),(0xa658dd5d658276c7b6e0,0x5d9a0ab886227eb0b2ee,0xddea93cd69b92f9d3885,0x6e9f6c5cf767163df7ce,0x8dd3fc2bb86a1409ab35,0xb4ed0700a0c191155386,0xc45d44d56fce15a21260,0xdf182b253b7eded80f75),(0xd612c446a6a3f11a28ed,0x1a8f350da33d307f1244,0x9ff2a402583c66e73bd2,0xe6fba34d8cc50a6e24eb,0x583f08448c615506e41a,0xfa92e1066bfe332f1845,0x750e8df18f3751fea599,0x7869252009ca507925a5),(0x2ade3b4a5910f67767e5,0x44374a142698c77411e4,0xa44fcbd24e6939bdf9ee,0x4c3d443902ac2311c8b3,0xe38cc50a3246e0f37f6d,0x7851ff9354d5fca7a5d0,0x7b46481d689e0865f9b6,0x74aaa28c4bd98728576b),(0x4f2c954bc2291acb641,0x39a7514094fe151aad7e,0xbaf11bd569ae264be219,0xf4c18f3898fabc2c7070,0x12752bb87c97a48ae31f,0x8bfa20966cc3d8ad8dcc,0xb207783f8504131bb50c,0x3ee470f41c11abf56411),(0x91f9df756c73b577b915,0x2f6f81e32b940271d511,0x10d3664562cb60d54d89,0x7f7803a07660e26bd115,0xe51f8f32cc9dcd555de7,0x794ba6b018026ec30b54,0x6aa1d06757ea6678de2c,0x3cd86327f2175e17fed3),(0x1fb09825b05c3d3d3efd,0x2d8dc049b08f16153200,0xdf4eec758987be462008,0xfc5d5d61895d717f6cb2,0x91b7b6175acc40b6e7b0,0x9577af1fd1c71ebc8331,0x130b297cfb961a83c75f,0xa187d932ee25b49ac34)),
((0xd3f60ca29c4fc9539bc4,0xf5ff48d210b5538061f5,0x182cdb4da11ce4ead5f6,0xc2f20d60d60f53bbf202,0xe3e00ce534925c49a105,0xe505ecc862036415832f,0x35e1052ca45a76391703,0x1fdb7940ea00aaeb6c00),(0x8a507a9608de0b72d915,0x1f79cf2c7b8bcf811046,0x87667f6be5db7d3ea6f9,0x6f0db05f3a196115bc06,0x18087bd70d2682b7a7a6,0x8364237a532c22d052d2,0x795996587fd930bc7455,0x3ab8594ba4ddfba7ecd4),(0xbecd605221b748ce35ea,0xebd52a25435f07a90fb6,0x9a6da28793624c50732a,0xcfaf5a055901a6fac3c,0x6cb731baa99504ecaa3a,0xaec07edd0715beca583c,0xe00f8e5542af7c04dca5,0xecd1591c8b28f81e505c),(0x899177f0788879faa22b,0x1057bf2926324a87cf0d,0xcd7d0f776bd57b9b831f,0x4cd27a51086e38f56973,0x4495aa86034e94356473,0x47765d609bd6121d0a59,0x2393ee14820c32c0d7a0,0x490d5fdd573d6eed4341),(0xf6da7e6c1ccf48a28913,0x3addc55ffc400fff804d,0xe96702f73ea14b51d2ca,0x34cedc0f5fd283da4af9,0xed47f4791aacad13a495,0xfb456849fb22675e35b3,0xd522192138d175635d4a,0x29ac4dcc1b2f460d26bd),(0x6363e0c351f40a58d059,0xe1cdb40bb8521279c1fe,0x6d9ed135c6cd24712da0,0x62ab187de14c87aee9f8,0x356d504fec08b65ecf5e,0x31475f9f7ea19d8b5e6f,0x7125b0497cf0205592f9,0x5132182022fc0b445c78),(0x79eea109a0142161018a,0xaa519b53c60a14000022,0xf4bbfc0a87948f7626d5,0x9c92e358419a7c482669,0x3b215231ff74074a3d5c,0x26262f86e51894c66693,0x9381f165612a389c326f,0xefdffbf782a8f021ef0),(0x7e6485e67b8f4035914d,0x882e104857417112c0a0,0x2edd10e8d98ebf95489d,0x8cc0d543bd6222df5dc5,0x91be7338c27625eb7e6f,0x9df51a48c943ab67a62a,0x6097a3b6f22288a2aba3,0xd045ec8e3fcddbfdaab)),
((0x66afdd2e3494fc3c765c,0xe4adc132016446047941,0x628f866c6ecbf421509d,0xecffeaac7eaea5ef0cbe,0x26f7c8a90bdb768fb232,0x43e9f3cf0e76dcfc1ab6,0xd9f07f600cae0532d437,0xc63a4d5daee0147f8f38),(0xad66b805b2fa01210168,0x965244c07a14666a04e,0x39df7a41410ea70ce601,0xea4060b32a1f785ad51c,0x4f7c75812e65a33e57ee,0xd2fa2d1603650b2db9e1,0xee81bca33199f026b62b,0xae6a40b4ba995bc6fc29),(0xb85152b83311a7682176,0x6cf78791099a63c20121,0xe171f06966223f40f121,0xd5c90366cdee3f399a99,0x8303e63fbc6170172b87,0x97b8f703419f75e7428d,0x66a751f4f75a5fe28649,0xbd7971b18781036fdabb),(0x68d0613d51dcf90ac5ec,0xe46605225de2b55ea558,0xccf092743ca4ebf8774e,0x7c2bc32f22312073162b,0xecf0c5b4fd9535bcabec,0x895f5112fec1334f9714,0x997c0e3f6ee88e927c0e,0x1bdb0a3b11285205a907),(0xc6b30f66d98805599a8b,0xcdd0778154ad9bb903bf,0x993a03effb5b06835366,0x2944885e04ce44b29a51,0x71cc07f6213fcef79ee7,0x220123012b68b0af35a4,0xdcc85292f9c1369cd975,0x7694e7aac1c3ababeca8),(0x24dd1646efda48fd1d16,0x330c62b466bac20a0b59,0xa8e6fd58bfb1f7d75a3f,0xf9245edbda74e849c46a,0xb8ae24313077114bb66e,0x26c41070afacb97632e6,0x14a341c3ec11e55bd1fd,0x217df4d83b3db98120b5),(0xf30e02ec00f1d101ae32,0xc5749f350501f1c22abe,0xd1523e26cbb7aff7cb89,0x4341daf4675f3488d53a,0xd159fd6d9143745851e9,0x42e4dba9eedf1e2dfdd8,0x85fafca28d98adfe592b,0x256084616de1ba0650b8),(0x1c7e7361ffe84fe801a3,0xd48819adb38d23dd5811,0x7eca2d3efd8916af857c,0x913f19cba07b00803a05,0xa8f4558e7344daf0286,0x946d11f798eb41f0685c,0xc28734886b973595d598,0x332d92d6515d9a44c244)),
((0x1243747b796fdba54099,0x384488f6b5ffdaa8e832,0x373d18550c0fbc4c0aa3,0x55a5eacc82d955fef4d7,0xe947906d1d6080aea574,0x185ad7573dcab422140,0x5227da4a0d6eb102daee,0xf8906642e177be1add75),(0xce10bf58bb132592520a,0xc41efd50ff4b42b40bc5,0x44c75f1a9a1cccd734b1,0xdbc77a2649c9a1403c70,0xe231a4af1695303dad3e,0xcc30e51d9f1808391e6b,0x383e7e479afb92b19b94,0x139ed2d8c0ac984a344d),(0xa1ca95ec3ae2d3114273,0xc5c5766c85638b2b9cdd,0x44dd31bb3b81b6ea2c0f,0xa65f08480dbd634d75f7,0x21c4a88681e9083d7709,0x8a21f1501124537042c3,0xb314baff530e22070edf,0x311ca97defc52e61438f),(0x4497b318c48ceb0c7e88,0x31d0a333af7c581f9f4,0x175b689738344b792d18,0x4b4f0268d6c49b4d5184,0x45774d9762866496ca86,0x1e7ef20a674c6040b9a2,0xc6c064674238740ee64,0x172903a431cba92cfe29),(0x2ee153287f6360d0eb25,0xc365d34dffde8373463b,0x34506800a9f37b0067ed,0xe40459b6336ceb6d4d70,0x43dd7c9bbc0d025d8c1d,0xdac2bf36daad51c1ee4d,0x48fc16b0569115857a7c,0x941fae30ed7f33f2cc97),(0xc8f9d14a33d0257800ac,0x1261838f9324bac582e6,0xaaa6c93b9f039884951a,0xdd943026a5f4aa19963b,0x782126f403a5e007e468,0x8a1ad58c7240e4b61fa1,0x5f0730ce6a3b5ce4e554,0x90d3747c7c913f20b383),(0x6207cfa875eac281a0e9,0x7a4aa8aed192aea65123,0x24c1a9bc401e4aebbb58,0xa0730339d69ea0c46315,0xf862833335f9015dd399,0x907d4ffba07b08722d8e,0x4e18a0e22daca1f959c8,0xc8fbcd1a72a51d4a4abe),(0x2b89d3346380df69fd79,0x64dc0ddf9aa5d3fa7472,0xbd5ca73d61b6cdeb740e,0x2fc360b24f0c9e50704d,0x84dd9af94737170c012f,0xd2ec94be0363f8232200,0xcce40a8d2160249b42e8,0xce96a02726d7c8bdbd87)),
((0x3ee6116ee007e03eab68,0xbbdc5b2c40f46cb1ab41,0x6835183444f847847166,0xeeff8450ee3a4a66ac90,0x326253296d8bd8b69f3b,0xa62069ed2ae75b9c9782,0x389ace9b1afa68a068ab,0x4df82c3952e22ed1e67b),(0xeb99067e4931a699fadc,0xa5174ce7cbf13dd0615e,0x9ca2aeff5094a1200a94,0xd67b4591d7c351533642,0x270b37274388e67d9fb8,0xb148ea1e89d21e87c3ee,0xb7f5f3437f103d1c74a4,0xf8f0412a3955fb39b1b7),(0x49d005f942ba34a78671,0xde62d89d74177ee0855d,0xfdf88c9469d3d3400434,0x30aa857a551c8c94db40,0xd8cd8109634405bfb986,0x7dde507a8a43ed6ae974,0x23200cbfc6635b4719d8,0x70a7bbf81b20ea575c55),(0x7367306482f73476208e,0x50a972c8ad1f954f22de,0x6db0a54d344e6f81a531,0x5d2673d82cae5b38c18d,0xb9dedbc6943262672516,0xfca8b661d53ea055bd3c,0x85170210850643490a51,0xcc42f41a8b18fd7becfb),(0xaafac90748543abfcaab,0x13e66241ec3964066c18,0xf5a477ead70c0be9c542,0xbaba545ec595afc3d6f4,0x7e17ac71afed7eb5c751,0x3cb6d28a332b1a724527,0xc9066d46d0ed57b26a10,0xa35de7a4bfb2b12a36bd),(0x734767097d0de1cbdb46,0xed333c2e213a9078dc0b,0xcfecddd7c0970ffdf70f,0x40dd9d6c7125e8b73248,0xcc9bdb8f59e35b3c1138,0xa20cdb7c2018f059e668,0x9e3dbca8de3c22eca531,0x45a3c4d3d232fb2c330e),(0x66c8585143ab4c03c47b,0x2daa4fe29fc373a55f68,0x3a48ec82fc9104ed2f59,0x17c92e539887d7ff9cd4,0x486acee559b853fd2933,0xbc27afc6fc72c959a4cd,0x3974e4eb85f730811753,0x2a56c02306d71a81b5fd),(0x9417f9b7fc68e9379d62,0x1c734f8b08886ce80901,0xdfc84d1b774943e889b2,0x5ff70ec84b92d5a60979,0x582dda475be64b895f3a,0xbf3a4e40957ff1065ae4,0x93830ca8a11f74a11f98,0x7cb3d2dcc8b44617e6d6)),
((0x32e2cedf19b32f0a5f61,0x95414d8a9b103c07fd47,0x3a26243f89d8e24c1575,0x68de088c3847c88c9167,0x197a3b06988157132d6f,0x9e4b92552218ddabea56,0x2d1e3913e4de8cfde9c7,0xf7225fdf3a22581d107a),(0xef210272433010c6235a,0xfa04ffca0cfdd7ecd1a,0x844385ddcbb01fdc1ae,0xa7b60bb5d74eb5216c3b,0xbc4d844fb13cb62b3881,0x28d7823d62c8379d3d25,0x6732f53d98b157893873,0x39223ecf68ea395a232b),(0xeaa84e12daacdf5df2b7,0xb97bf7c4c5872e2ea870,0xebf3675afc009726d723,0xd206841de16f32952298,0x971e07f42ad93426b2a,0xb7f8c9ab8ec3f7d15d5f,0xe732eff3797b0303c28e,0xd1509ad47a3fcd34639d),(0xb8a5ee4df25e99e23a89,0xf0a84f59326c18a02ceb,0xc89bf692cda4765ab309,0xaa78182066c05afb94cf,0xa72ab48cdf3720f275cb,0x6742622a6dcb3c365569,0x8544291f210d647fd649,0x4fe4d347a27eb0b389c3),(0x94660c7b40d70ddfe840,0x68167d19ddbc21900bea,0x8667da0af0b5f6c7dbc9,0xb5ea9edf4672d11d62de,0x98a30ac3b2a245202cf9,0xf45be710c396f019f062,0x33a972634ced1400b30b,0xcb5b076ce0001b6c0b74),(0xa67091dc7e8d66fd74fa,0xde601ef38b19cd0ac51d,0x98d5273c0d4bd249f052,0x176c9558ea2aa9bfb80b,0x8ae082ec0269b52f2e35,0x3905c2f2e458f688d20a,0x9ff369a5a5a3f771b3bb,0x33c9cf72033665e55db9),(0xf4354017c476e0f262d8,0xed1930e3bee154c4facb,0x615b946b31dafd41c37f,0xdd800d17d1d8388730e,0xde99f84ff04c4d98ee02,0xe31d10cf0ca45e25660e,0x726065b6625479e073a8,0xabc63cead44cad3426e8),(0x103a589f6b86f66e8dcf,0x20d006187671463cd72f,0xa2e2f69e149bde0a6ac6,0x9102ce2126cbc60a7331,0x2e1c46be9a1ec21d60e1,0x1099b6ba851b51dda45a,0xa2a6478bb36b7dd15836,0xe1b2c186e1abab13cb8)),
((0x6d46f7aa8fbb5f21513f,0x5849d7889e8890a72794,0x68c39f8b4f62c7d15a1,0xdf86f8e0f096ef8209e4,0x7bf591cde71526e6a294,0xec06b607f67e71f71413,0x89e1f4ea9a7827cf67e9,0x35e886b996920958d9ff),(0xaf7dfa3b2a2cdc40d830,0x79f22b9181cb0d641ccb,0x457c80885472465e1db0,0xa63880bbfd95f710985a,0xf8e7aec89adaf7e05c37,0xeaab808af436d5da0d96,0xc5c8a95468ca502d9790,0x202231628e49173a8ea0),(0x17b26fe216514f0f7195,0xdbd9d7b18619ba70db1c,0x9617f13277c6223d82fe,0xa03b2320037795df5cb5,0xbda43a03e6ae38b92b2d,0xde06442d3cec55beb882,0x7eaba91c7c9b3cfc6d2e,0x8d496581b760cf03fe99),(0xf6c16a0908eec629f454,0xf27c67eda7fa4b1c9e67,0xfe34939399c2c8c90a4,0xf44c7943831c4d4b22b7,0xc7be72c9cdf2de205a1c,0xaa7b61060455d1197ed,0x5ff91cbb9df5b932911c,0x5d870f546b297f960361),(0x4c18e74da0fafad467c3,0x35a642068e3486c4ede7,0xedf2dd66b7947a7a0ce2,0xa62cfc7671c022625f00,0x8e62002e46359a8bc849,0x19737535f9276e9345a7,0x8b5d7bd38f8b1c40a24e,0x5395ebad756b4acda9ca),(0xd75bb49ce4f00171829f,0xc62432ab4ce0031eda14,0x2c84bc876d338912721c,0x47e63663ff902e4057ca,0xcdce0b44d76ea96064a3,0xb629cbda1d50e56a899,0x784be13ce0cb5cdce563,0xffabec9ebb37fde0eb0b),(0x9164327dd491b09a5bd4,0xd902cfd4c844c451bb0d,0xa6f01ebf37df9876df9d,0xe05b152721226c66f0d0,0x9ba4f8f3a5224eb9c256,0xddfeac293e2d18ceb57f,0xd5383e8a229dcd5475d6,0x16ca3f658a2128e38483),(0x49dc47dba033db531ed3,0xaa5465479662c1770065,0x8e0374b934f20f6fcd97,0xbf3f57c18b24121029b7,0x2c3a555b6e064a3e4574,0x6b84a6e65024ba7f8f80,0xcb936b5087a6bfdd1cbc,0xe360343143289d2eaf4)),
((0xf1b336439953e85cdf5b,0x8a429c700b070f82df89,0x50992c5a2a8d211f36a5,0xaabe22c90fd3cb08d58c,0x7a99a5b27fbe1ceb5ca9,0x45d456e0cfbf6fa4caa1,0x1ca07f4513b37f28e6be,0x3b63c963e9397e179350),(0x20a5ba8a22aa5ce0801f,0xa1e41eab090d6c67f3fc,0x79dc5b4947ddb82e0922,0xa3ddcf217388a0b12b05,0x943710bd7e25167aa57b,0x66a155ccdd25a0f8d7c2,0x78d26c6ff7897b60f09,0xd88a9ed12f7298b0d3b6),(0x2949754e0ee904457c85,0x4c45f211d46d7e799d00,0x95930cebb49867248821,0xc5d6fff725137cac264b,0xb385f67586f051158759,0x27342403b5fa00349f9f,0xd17cb38f09e456ca76,0xe67826c2c6ab6fd9626b),(0x9ecde777f32d90dd3ce6,0x6be224e9a08126274ad7,0x2c26c4d6c99b6b1df21b,0xf6fcb64a67dba760e3b3,0x7c8ec364615dea87f652,0x4b10a19220d6033087a,0x7cc641bdc60069e1ab11,0x25cdb8d78244932b80b8),(0xf31b190d168c6ebcf643,0x8e4827c0f94bc4e4fc72,0xa588ed9b293092eac984,0x4609d3590d3f623a9627,0xa19e357b53b577534df,0x56e5d37102ce8c9c9f08,0x515d31cc905ef89abe07,0x9df19729a2a8342f4851),(0xcf76f53ddf24090745f9,0x88c4e7e54433a4bf5b18,0x347173bbea43e12983ed,0x74c59d49a1c8c053a32e,0x5fa0c34241f2327ff89e,0x7f5b29c6fb9009e6d96e,0x50850e73b1147c67d133,0xe650b3b09243d43c06b7),(0x68065e90518f2c8b3c66,0x919512dff78cd33e114b,0x3b8b9a8071b331711008,0x9a59fb271dc7fe82d00,0xcf64dcf7840ac25ea0c5,0x244e8a3257c7c656c26a,0xb9ccb2ad9ed9b4e6b628,0xb3db4a840b9711d55f12),(0xecc9b94e963bf4d05f64,0x3203e9b69ecdbb7dc83b,0x82b89aa1aea55cb9efd4,0x7b4c490c583f282aa8ab,0xd8274b419aa535dae854,0xe8e168e31710ef1f1f89,0x99f246457f71a53742a,0xb8d23ef06aff94b1877f)))

def page20 : WordPage :=
(((0x14ce1803a54aef6b247e,0xda1958c9d4607c72713f,0x20137663832508670bdf,0x1772506a2321445fd44c,0xe2b97f2bd4768a0ada18,0x6535714f3f9e4dc8db70,0xae51ddb85b0fc9411a6b,0x6c586ca11703de5826c9),(0x70f05665cb09348b95a0,0xe05ccb1be0965dae079f,0x395d461f002e153a472f,0x31a29032322ae2a0afcc,0xebf033b8e74342199b21,0x6e9796f4b39921a79df8,0xc61df631b812267149ef,0xc844b909e534155375d6),(0x871f462c5c4d352ffd98,0x6754e8ee23003b96d02a,0xb8272d6e47ebaf89bb92,0x20b88a44adad37952af2,0x9600b714d7f33212150a,0x92f529c60127a9ba643a,0xef3d0baee595db7bd1c,0xca61a37d796fe71504fb),(0x67e1fc9f4dec5b166216,0x817fc4fd928658ec3cee,0x95449313041d0f4ca2fb,0xf44f26b0fbb429aa06d4,0x92ffc15bd46d69d88454,0xcda6e551cdda3bbd2329,0x10f26da41c2e1e553a8c,0xb75daff61b136f9e5df0),(0x41737c4fc2e4cab15a48,0x5102b5f3b1c9ac1d070f,0x89f6f2b9ad1528bcc478,0x9386a858b4b1a4cf9fbf,0xb7d7624a1bf6ea119e08,0x9fd8e85a32b7335df882,0x9081b3416f83a0152a6f,0xd878b57e3f31997be383),(0x2f7eb0a5bad18794056,0xec86cac70a17964666ce,0xbb9e6161d26db0902942,0xe4e5c4d955edfddbe87f,0x736b0fa25ef2fc603fac,0x8da102b5b077e63364d1,0x14220109201d8b3edbb4,0x3d7af9f24702fe650878),(0x43120da1517a9f19557b,0xe6a4e7b56e130ffa3c7f,0x381486aba0d37dc1fda5,0x8706b723fd3913846dd7,0xd495b8685ad63828c695,0xf8bea86f2aa93b4c939f,0xdf801d640978993a6f0e,0xd26f69b4e21e4245330e),(0x22c05aa91e0b1c096203,0xdaa0f6a07d89084704e1,0xdd9832b04a07bbe4f74,0x5e28fc2853b2993cfc25,0x3f878269aeb14faf588e,0xa07ba150a12aacd8e06e,0xcc7b7fe2da94fee51710,0xc699fdc1068ab13f0703)),
((0x62e4a3337d8defbe55fe,0xed3a7f88075ae5a96c56,0xd0dae18db15a9b88d07,0x6a97880df92b019cc211,0xfbdb1e60ff4d06f7b5a2,0x936045e3ba39480165d5,0x799d86b73d38b969a48c,0x8ac8cc76719ee939b4ec),(0x6435c5ee28b01be265eb,0xce56b9fa989079fd3912,0x4ffe6523c21402ab4330,0x21ee754681fe9f9d2cd7,0x53c152327edcd521dac2,0x1d97ea223a4b11504b33,0xf0837b35aa22fb38df81,0x2d472ddc918b4adf1f4b),(0x36b144cf7beee6737e91,0x4fcd7d8e3ed47289c199,0xaca31ecbc18f4925f3a,0x2fc330f2743884137911,0xe10263b57e4f558e2ed7,0x1dc3ddd6773a657e330c,0xa9c228acf16d6a9c1962,0x224227d01842e5b084a5),(0x11e17f2409e11305be9e,0x17c74f3dc15524b4296a,0xa6bfa3370f0ecae82e1f,0x307bdd2c8290f0304b87,0x8b2b63c5bf829f0af477,0x73076d6a37dddaf2aa58,0x29a8cb1a05020ceaaccc,0x5869c9fe9cd4517b11f5),(0xddb2b30a2f9124c1b0f2,0xc7c6b56514e655bfb8cf,0xa8ba474e990194a83ff8,0x81a0dc665c96fd1e722b,0xe832681a7267f24b09ae,0x4af57d35e74979b011a,0x533368a96f38b91450e0,0xfd35d08e9f7001d0b76),(0xffb71d3a5ef36f423032,0xa586cfdaf702cb2451ac,0x7f5b7cb708f8b3bdc3e6,0x218eff151388bf8b613b,0x29f3eba708b12d7f8f42,0xa164bf656c26f66237f1,0xab915eb37c35cbca7426,0xf26fb979f88403268b98),(0x452c0bfb96c2658eb26f,0xbd84b4f33c4e4badda48,0x4ab51b32f674856c4840,0x7ae602f7bb31431509a4,0xfd81c301548679941ca2,0x833206956afc0c11e6a4,0x5a29f743e643804beb03,0x558e0ceceab948cf6139),(0xf230fb94ee5e696ce7ed,0xc8f3dcd806ba585d705,0x8e0a732e80c83980199b,0x49cb335f05cc2f6bb53d,0x664dbe7c39901d93bbfc,0x9ce91a935e4d7b080e74,0x61e00beaaf6e2b691ff8,0xc4058c1e2059cb5fe69b)),
((0x2fc7ed49c7e2d57cf180,0x61b468a79d7bca467b3e,0xad777dae9df2340e607a,0xf854fdc1b9c180c5fb8d,0x98257b2e5cf67ce9310c,0x2a10b073df9b26e7db5a,0x955e81ff4aecb2f54067,0x338fadc975ac87c2774c),(0xe955926ea06eda81a555,0x144530f4ed70a174b68c,0x7cb0d2f8009ec36b3230,0x88c8239010b3eae611c0,0x84f2884c341409fdda17,0x3cc3abf1ce05c4a1fd3d,0x94e82dd61d2ec4b0781a,0x3867b84f63e82c697ffd),(0x285df50d7125a133bdab,0x378ef5796b75961e5e66,0x2a4be5b0377e7dd1400a,0xb46f7f1ead78e1111a25,0x1ea03e0fa9005a218c93,0xf1008667c9bb7327f8d0,0x3318f61479b2e025e08b,0xab1f4d987aee99888051),(0x98c1cd176c0d94e5e9d6,0xc49b42fd9c0974c79133,0x6f7a1da6601231ffe8cb,0x69eed96c887ce391d710,0x939af42a698c7e481751,0x721aa8717df7f38fe8a4,0xf1c3d357b2782d6aec5f,0x33d46754d1f42401355d),(0x39fbc10f6f3f37bef122,0x93b3de2ad6793245687,0x6cd0102782cbf6ea5621,0x3b84f9eb33b3451e2e21,0x56afc3dfca3b462ef71d,0x29beb3864ebb089682d1,0x2020b0e44982ff981891,0xf48e631f9a7390cb3c12),(0xd8808b05204026aabfe1,0xce58b152ec71b8cfa9c5,0x419736866bcd1da98fe3,0x7fda19096c8179203611,0xe4b29f85486813c5416b,0x67a5b0e125ef1fee783d,0xab8a36a741287b81f102,0x1f118cbbced8f2f878d7),(0xbfaef958c2ddfd7d4362,0xd2d0681f5ae7e5c56b80,0x1b4159625d8fd50ac8e4,0x34d62459b90cfe0ab7bf,0x23b364a0169b43c4f904,0xa4bde2cc59c9d08f74c1,0xd6a32a7ae6cb3513205d,0x3e82c2bebd2935b31515),(0x7d05f062e18c72f9198b,0x47563f07eb3ee5b3eef6,0x320680705d95100cd41d,0xbcf9d866c929334596df,0x3dfbf40c653e568bed2b,0x3dba118587befac030c0,0x459dd7cf594adce4182e,0x85e8b8121de10f2052d4)),
((0xd952c16abc7f98ed072c,0x24aaa7d5da7be48df0f3,0xb6d2bae60d97fd53281a,0xf97a3905e0523d6eae9a,0x3aa6b6067ff5e1bcddff,0x209ca73cce1844762f8d,0x804e3dc56c0061fef08e,0x8fc699f9025cdec01534),(0xec73abf0879f7cf2d171,0xecad27f830183bf0df2a,0xab7c79dcadf3ab4bf8cf,0xa032ebe03d9ce486f451,0x4af341858e6f9ccf2a73,0x6b8c5ddec00b6fa76b59,0xb4b4a31d47f5a27d0db,0xcdaeb1519bc9de056e36),(0x83145ed190edba6639bd,0x872cadb2f4ae36d8783c,0xf5c2f91705c4c4d7fe21,0xb5375e8d6e26e12d89b0,0x8bc46ad742dd040116b7,0x1c384465ba3ae287eb7a,0xc1c58e5d0513b14ca981,0x3a4573521e7e3052298),(0x1fbdb457c6d2fcea6aa2,0xdc2557b354b92cece0af,0xcec52820f583a266c227,0x5c8c74fd1103944188c2,0xae5d605e6f4f91676543,0x445b1c883951e9e9bafb,0x51cbd352bef0bc2c84a9,0xc7fdf68815444c33d177),(0xbdd82d429c0cefd39b1d,0xb8055bae2a7e200085bc,0xb64bde0f94064fc169f3,0x3196571f958be1c4c7d6,0xec4ced9427797188ced8,0x1b8698ae609d10201617,0xdce076c582281db08b68,0x7539c3a58705cbd62522),(0x1dce5f581203347bfad8,0x499aa2ff1cdaf48e31ce,0x55aa43a778734c93533d,0xaa28ff08e2937b0a4ef9,0xf6bcf542ff9b1367875c,0x48d1e09062ee779ec472,0x3e989c836946855c5b6d,0x27246ba1ed42aaadab4c),(0xfa9c4df7bc28e061ee7b,0x169f56c4e0fbbd09cdba,0xd1f9ca44fba2b81e0176,0x677c10957644ba6d3970,0x66a7f891f9343752fd90,0xc234e51b519ecc7169f2,0x31c117639b6fe371d114,0x9ea718525762e375ceff),(0xfd2caec17c7aa2a752bb,0xc9840f8109144f3839b7,0xca4bd62916f63e1b5f34,0x556350769fe1a43eb6aa,0x5e4ea91aa2c4e05d7123,0x92be7497c85dfdeb82df,0xa092c36fd8a5504c5753,0xdd254eaea024fb9305d5)),
((0x9deeb8140399b0a5e52d,0x5540394d212651dc510e,0xb816909d86bee8cc2afd,0x1cfaec84855f3ac1966c,0x93aa5bb9dbc0bd5b0367,0x98470c4c75bc0f8dffc3,0xc711cfaeb62577446987,0xd0811d5a449250d5991b),(0x43d6aafc2143883e3147,0x798da8537c439ac9bb5f,0xa94088878fc502ac5049,0xec287acc82fb2d2fd33d,0x8e2dfc7b83e20d04858d,0x7fe9c47a7028a4b140bc,0x6f79eceb9d3266c0d1b4,0xa35e630405930c99e033),(0x314810c7e0b18b3d5848,0x5e59f4b29c89ca3a94fa,0xfa8ce0f0ccbc9268317d,0xe533324168e2be9826c9,0x501b05ebf4545db90bf3,0xa65c91d2fa5eac542d85,0x825f51cf8a78c8f3bb9c,0xa47cd11d0d03f625c28),(0xc7702c1001f87c824336,0xdd822db163c0d62a6c38,0x2e47d9de549e36d35424,0x6a278ffdc8abb5a49e0d,0xb00b1d08c9574aafc988,0x8086ae78760614a883aa,0x7adbfcd7413a9ad76ca9,0x11ba4e7eedd78a0e34cb),(0x6f6b2a88f75265429f70,0xf5e6548c224b6ff4d57b,0xee995a7b7ce1e2f20259,0x2b19b509a2f4da1f150d,0x764cbe4f672ef1e8cf89,0xc9d86c73b4b17eead49d,0xd983c370363caf0ad373,0xcb3ea58dae0258cb36a4),(0x5d88290de0235851050b,0xd2c55dcd5d1a0d68c9c2,0x19c998c487c29fb10695,0xf0c929e5672e0e1b8069,0xe2b57422c15a29836f6c,0x31af354630e74efcfe50,0x8ad448e5cd0bd32b9522,0x14c1ec0bd4db576a7cc6),(0x8a1b40835ac0dedb71d5,0x7cb6ce415a36e9dc64df,0x85b44eed33448c705107,0x783958617c86f2aed344,0x4947a8168577f04f7c12,0xdce2e2792220aa5a5574,0xe1a196dafc80b9468411,0x2c1676641ca1ad9fd4d0),(0x4b9d6bfc7f3200cdf7ad,0xb1b5a635f30d95dcf704,0x373c5fcacbac9a2b7765,0x5b0bb87b1b12d7bc2260,0x1932336aa698801aacb4,0x72198fe34c55cef7b44d,0x9839ab3f436997538695,0xfcedac35aa47bce6a13e)),
((0xbda37161ead236f4e60b,0x956e2f7fc4e337540662,0x8fe6205c4de765a93f3a,0x482c0dd6468b44601370,0x96085f6ccdbdb0756c3f,0x9e81f9ad550502fbf1d8,0xba98e2025c5652aea448,0x4e103ceb03da0c1c05ca),(0xf8b43e3dbcdbca0cfecc,0x452b038a4c398f989b35,0xb92208576905f888e971,0xcd9a7e89cc84e03fb8bc,0xe8482d864246bf202089,0x6b8f6fb9cc0d65413add,0x90b5bf1e86e732e05844,0x7ab7ccf6c3c801c842b8),(0xc3d22b3e200e546dc30,0x8e4227776dce009db519,0xab8e88c757ef8e04bb30,0x34fd8667a944114ec435,0x7366d4caf4caff6a9908,0xc658fa27e473826742ad,0xf77ec3a0b67082539906,0xd1e7dce75cb0c8f31180),(0x907890361a4d331827b0,0x542c2fb2bffa955e0aa4,0xc8621c6842ed2003b7a8,0x9a38535652beb5c2c2d1,0x86e212aabc9d9b7a5681,0x53f3e546181bf6fdb7ba,0x45798fb9dc7d6ac511cc,0xfbfd97180a3d26dd8bcc),(0xa7f4b17b7efdf2a925e5,0xe946a0b169a134338bcf,0x76cacc987b4c65f469be,0xd321694c7400b74baa80,0xce0065a028c377949f5d,0x2d5ecdb5c8044f9637ed,0x7419ad395b92b3cfab1d,0xb83f46bd5ee58a5a5df0),(0x4433ef7669247f33ae18,0xc6cd96353dbbd48c76f,0x41ccfa5ade9d4ed4eb6e,0x9ff0859b96a0f23941ec,0xab21c6342d99100325ed,0xe01f7fe93502178cf555,0x56e64cc35ddec8a3e063,0xb3b086274fbf31c81106),(0xa4c55381010286764474,0x8449472f21c84793bd9a,0x18162ccc7a3032629118,0xe5f91ebb6e129e946bcd,0xc5a8569e7e93f8eb90bf,0x1188debbe50eb3b8cbc0,0x88eaffd91a07ab6e0bd4,0x89c5756921dd41d67965),(0x335edab43d8797200d13,0x5f9fe6cc6863d8a35c34,0xc9d9d690e64a1ed21516,0xecb4385bcd31caef073c,0x4a1cbd21673e85891dd8,0xca5e074c8a5f8c9cc2ab,0xa8e37f87862f10914d3a,0x51babcaf2606190bbf50)),
((0x5c02db6e8e5538fa2e77,0x5c32498554d6da33d698,0x7333e3d300b40c0d866f,0xd24cabf4dea3be24c551,0xe217e0b6ec143a58659b,0x99e5afc603cb30cedf17,0x52bc9db0ec20aaf480b6,0xa67f59c701300377de66),(0x11167b5c923bf01609a6,0xe06578363bb6a950f7c0,0x1e1563701e890046f1af,0xb8121d893081af4e8758,0x9dd4f1141201b3c2a36a,0xb9cc02e06732bc1ccaf5,0xea9d1e36899902b4603d,0xc9d989ab866cdac2a10b),(0xea97151ac3da4c4e6f9a,0x54e499b61639d8e3908f,0xc7d90eb12cfab3a12666,0xdb4c33ecaba6a46e8d45,0xb4139c9cf08f087153ba,0xe0e40d47d8b2a813ea23,0x75b199c6de449501966f,0x23cc8dd6d8ef25dc74a2),(0x540077e43d56e4f6573c,0x1db638b6eccfdfe46624,0xba147b9d2e4224300087,0xa169a8c2fba144a160d4,0x532b841a6d35b08327c1,0xcfd5eacc7e78a851f35a,0x9d3c2de338f18fa624d7,0xd10920c379ccc591883d),(0x8ebefd5b5c1be1bef64a,0xe6c1e98dbc75de22818a,0x42694d9a728c625e3f9a,0xa8900b9133a8e3a06460,0x592a80c7d7447db4abff,0x5425b89e689f6a8fb90a,0x89b3345c0d5e761793f8,0xb6036fed5e0d2ccfbf9),(0x2706cab29bd07978245e,0x43f9117d8dae89196cfc,0xb3375f3a98d84160d928,0x3ebe24b3f54bfd97453f,0x8d5066009828bfe7c597,0xb4374c99f97378d7afd2,0xce50b67671a19716c6a0,0x77068437cbf3b516c87b),(0x6c0a59e02eee41e252e2,0x41c666dca54040082da7,0x5c791aa1fbf59220088a,0xc0757d115d9eeb702883,0xb359498ed8c77e54d171,0xdcf7e7d5393be6abf2b,0x7ecbfe08026cd5f8a13a,0x11df0e206ede1477e31d),(0x38d43cc3fe4360e716d2,0x58e211f460e10512544e,0x3002e45575569a8f7fbd,0x134e7fddc0d145aea698,0x8f1a876e0e2e26a31722,0xaacda88928713ab17709,0xe73f965ff87f718f293d,0x8d4d58e206e32347fe31)),
((0x64c9577e483c9169ffcc,0x3455f785feed87236133,0xab70a490eb3db92fc3aa,0xff86a84d190ea080ba72,0x265c402d3c724e793caf,0xe1fc48031ebc93d6001c,0xdea78fb5f2f5790dc837,0x397c694a468b0b250882),(0x7afd27ba3da988714fba,0xfc1dbaa301240c025eb,0x3bb8cd1a232544610f84,0x564e5c83d94e4a0e6ec9,0x656acb6e6bf6fdcf581e,0x46a106da2f6932bdc3f3,0x7981251235eb115f90f6,0xcdd36f3d2b5c8bf2941a),(0xc9da584a9c300cf71452,0x18c40b7141f4c1d59e99,0xfc7767c768229cf39f3a,0x81c4208b70a1c2428834,0x8e8b0a5a9d5753d8fbb1,0x600765de95c1f27d919,0xbdae1b68dcc626ecbfa9,0x912c218df11830533e61),(0x5103532f6c587eb30f86,0x36fcbb6874313d638aa6,0xac18d9e96ee77dce13a7,0x3be9ac1b092aaf9dca61,0xaca7e5cb94df5372ed78,0xd76684e4ecea6a1c1573,0xffd8267d9799413508fa,0x36e66d600eeff060f307),(0xf55dbc596a15d7984d98,0x4849a10fb4606d3e893a,0x3aa91ae30d6fb1aa744,0xf342bee6a5c64009a24,0xdac41b2bd9505b738a34,0x6299a9aa3f7e87932302,0x370ce017b7e67bcfefb7,0xaade00770a8ebabb8e26),(0x7408474c7a34ef4cf9a3,0x6248344ec719107366c,0xa78a8ec9a12beba56cb5,0x457b027f822d31d8df1a,0xdca2c25905083b519e5c,0xdeba74d523ab48a58bf,0x6c86abb4567a392d0b6d,0x688e4d1306bdd040b8e0),(0xc45cd2144179fdb809ad,0xcfda78dd4687c28a7faa,0x98ae0f064534409c461a,0x1c79af03ae67b019cb44,0xf818825458a096b92f2a,0x594ca2c5285ab53170de,0x5b3fcd07b00f6671244d,0xa70b8df66ed53581f3ac),(0x4cfc5f04965a8694f161,0x4b13f43d8f4ef6a0da00,0xd2aef887de3228981b50,0xe150081f5418d4bbb10c,0x8410ddfbc8c05976462a,0x21bb985baaa0ebe1d299,0x870a8574ddd41af191f3,0x695dc5f3a15303796d2a)))

def page21 : WordPage :=
(((0x69ff0a8fe78e906d21f8,0x601c72a4fc0fd80ea96a,0x48d7909338782025f6e7,0xa90285108ee145efa1c8,0x5b50c78fe7152f791b37,0xcb7c06228ce313a1b202,0xc31165eb128ee4e58ae0,0xabfe1fa7c67a7936a4d9),(0x4f4a2efa062440e6b0b7,0x20fb06750af9280f3a4e,0xb0c689bfcfa70dbb7d08,0x59b2921894d6f4e21ff3,0x13ac96df009dd3a8c3e2,0xca28b5b01ab231152d74,0xf141a1ddddad2e009216,0x21d8047317f804974ac2),(0x3b65720a22397b9bd984,0x5d71feda07a8660745f9,0xc9262882411538c2130d,0xebd5dfc97c94d47f8e88,0x4be6681d92ff23a9c540,0x58d77bba5ed515b062d1,0x3432bf1c3f9b3f82b702,0x591e916ee1b33668641a),(0x1ed14ca66aaae6171015,0x9c0eb1d74d1056114ef7,0xdade62d81172111d3adc,0x35490c045465c27bed5c,0x979de41a1c58937573f2,0xcf712eaf4e15bec1361d,0x5fcf48b5cb34d9735079,0x2d56ad9e089e6fe047e2),(0xfbae62d2dfb1aa2b58d9,0xc1babebb30bd4071762f,0xcdcbedbb99d3ddf53cc1,0xf59b18b75640b08967f5,0x8e592122309728124e34,0xdb93a481b9afc230a18a,0x3270d2e50ad6f7163082,0xf51d2c85a5e98f77800b),(0xdda191ecc1bc90a204ff,0x8bafb7a91264edffdccb,0x58c0b23917d61de2d281,0xb35067ca91f99b3,0x1000301000201000101,0x7010006010005010004,0xa0100090100080100,0x1000c01000001000b01),(0x301000f01000e01000d,0x40100110100100100,0x1000001001301001201,0x4010016010015010014,0x190100180100170100,0x1001c01001b01001a01,0x1f01001e01000701001d,0x220100210100200100),(0x1002501002401002301,0x28010004010027010026,0x2b01002a0100290100,0x1000f02002d01002c01,0x1301003001001101002f,0x320100150100310100,0x1001101003301000f01,0x1a010035010013010034)),
((0x380100370100360100,0x1003b01003a01003901,0x3e01003d01001d01003c,0x4101004001003f0100,0x1004401004301004201,0x24010046010045010022,0x480100210100470100,0x1002401004a01004901),(0x6201004d01004c01004b,0x5001004f01004e0100,0x1005301005201005101,0x5601005501005401002a,0x580100570100210100,0x2005b01005a01005901,0x5f01005e01005d010046,0x620100610100600100),(0x1006501006401006301,0x69010068010067010066,0x6c01006b01006a0100,0x1006f01006e01006d01,0x73010072010071010070,0x760100750100740100,0x1007901007801007701,0x7d01007c01007b01007a),(0x8001007f01007e0100,0x1008301008201008101,0x87010086010085010084,0x8a0100890100880100,0x1008d01008c01008b01,0x9001008f01007701008e,0x930100920100910100,0x1009601009501009401),(0x9a010099010098010097,0x9e02009c01009b0100,0x400a10100a001009f01,0xa80100a70100a60100a5,0xac0100ab0100aa0200,0x100b00200ae0100ad01,0xb40100b30100b20100b1,0xb70100b60100b50100),(0x100ba0100b90100b801,0x370100bd0100bc0100bb,0xbf0100710100be0101,0x100c20100c10100c001,0xc60100c50100c40100c3,0xc90100c80100c70100,0x100cc0100cb0100ca01,0xd00100cf0100ce0100cd),(0xd30100d20100d10100,0x100d60100d50100d401,0xda0100d90100d80100d7,0xdd0100dc0100db0100,0x100e00100df0100de01,0xc20300e30100e20100e1,0xe80100e70100e60100,0x100ea0100e90100c401),(0xee0100ed0100ec0100eb,0xc20100f00100ef0100,0x100f30100f20100f101,0xf70100f60100f50100f4,0x1750100f801016d0100,0x100fb0100fa0100f901,0xd30100fe0100fd0100fc,0x1010101000100ff0100)),
((0x1010401010301010201,0x8010107010106010105,0x10b01010a0101090101,0x1010e01010d01010c01,0x1201011101011001010f,0x1150101140101130101,0x1011801011701011601,0x1b01011a010058010119),(0x11e0100ec02011c0101,0x1012101012001011f01,0x25010124010123010122,0x1280101270101260101,0x1012b01012a01012901,0x2f01012e01012d01012c,0x1320101310101300101,0x1013501013401013301),(0x39010138010137010136,0x13c01013b01013a0101,0x1016a01013e01013d01,0x4101012e01014001013f,0x1310101430101420101,0x1014601014501014401,0x4a010149010148010147,0x14d01014c01014b0101),(0x1015001014f01014e01,0x54010153010152010151,0x1560101310101550101,0x1015801015701013301,0x5c01015b01015a010159,0x15f01015e01015d0101,0x1016201016101016001,0x66010165010164010163),(0x1690101680101670101,0x1013f01016b01016a01,0x6f01016e01016d01016c,0x1730101720201700101,0x1017701017601017502,0x7b01017a010179010178,0x17e01017d01017c0101,0x1018101018001017f01),(0x85010184010183010182,0x1880101870101860101,0x1018a01018901015101,0xc01018c01015301018b,0x18f01018e01018d0101,0x1019101015001019001,0x94010193010192010118,0x1990101980101970301),(0x1019c01019b01019a01,0xa20101a103019e01019d,0x1250101a30101230101,0x101a60101a50101a401,0xaa0101a90101a80101a7,0x17a0101ac0101ab0101,72057594054814977,0x2b0000000100001200),(0x100004d0000000100,0x690000000100005e0000,0x1000085000000010000,281477661065216,0xb6000000010000aa,72058500276027393,0x1920000000b0000de00,0x10002d30000002400)),
((0x880000000f0002dd0000,0xe0003c1000000040003,281493431648256,0x4be0000000700045d,0x100004ce00000001,0x5c50000000500058400,0x40006200000000b00,0x7e000000010006740000),(0xb000737000000140006,0x50007ad000000,0x8670000000500081e,0x700089700000003,0x9710000000500090600,0x10009ab0000000400,0x2000000060009bd0000,0x1000a2f00000005000a),(0x5000a40000000,0xa9b00000001000a73,0x5000aeb00000006,0xb8800000007000b3800,0x4000ba60000000200,0x5900000005000c060000,0x24000fa30001003f000c,0x4f00131b000000),(0x16fc000000180015f5,0x4e0017b700000017,0x1c7e0000002d001ac100,0x6001d620000001100,0x770000002e001da70000,0x160020a0000000020020,281618438684672,0x21d700000006002173),(0x50021e300000001,0x23420000001b00222d00,0x800234f0000000100,0xa50000000100239b0000,0x10023f3000000070023,0x50023fc000000,0x24ca00000009002442,0x60025820000000d),(0x2624000000070025dc00,0x10026600000000400,0x970000000500266e0000,0x10026c8000000040026,0x70026d4000000,0x27660000000200274b,72101767776567313,0x28910000000700283a00),(0x900289e0000000100,0x4a000000070028eb0000,0x5002959000000010029,0x5002991000000,0x29cd000000010029c2,0x5002a1200000003,0x2db000930056002a5200,0x36002dbb0000000100),(0x2400000006002fcf0000,0x500316b000000240030,9570362832453632,0x334e000000060032fc,0x40034eb00000031,0x36380000001c00352600,0x1c00368f0000000600,0x70000000030037cc0000)),
((0x100388e000000010038,281718330228736,0x38d0000000010038b4,72120141646659585,0x3910000000010038ee00,0x10039f80000000900,0x9300000018003a020000,0x2003cca00000002003c),(0xc003d79000000,0x3fe40000001b003ebc,0xd0040910000000d,0x41740000000d0040f200,0x80041e40000000d00,0x7c000000080042340000,0xe0042a7000000020042,0x6004368000000),(0x43bc000000010043a9,0x60044700000000b,0x4505000000090044aa00,0x20045690000000800,0xaa000000280045800000,0x70047e9000000080047,281785204211712,0x49eb0000001c004846),(0x47004a6f0000000b,0x4d840000000d004cd800,0x29004df20000000f00,0xa900000003004f8c0000,0x10050ba00000019004f,0x50050c6000000,0x53540000004600511e,0x2300565000000040),(0x57a40000000100579a00,0x10057e30000000700,0x23000000070057ef0000,0x630059890000001f0058,0x5005cd400a600,0x5e8b00000029005d28,0x1b005efc0000000a,0x632300da0083005fd300),(0x4b006681029d002c00,0xb80000001c0069f90336,0x31006c0b00000006006b,0x7006e14000000,0x719903930053006e45,72184609105772570,0x743c0000001200739500,0xb00744c0000000100),(0x2e043c00670074a40000,0x50079030000000d0078,0x2f00794e000000,0x7ab300000001007aa2,72192894097686538,0x7b4c00000001007b2d00,0x1007b6b0000000100,0xa700000001007b850000),(0x1007bc100000001007b,282006915121152,0x7c1700000001007bfb,0x7007c3700000001,0x7e8d0000000b007d3e00,0x17007e9c0000000100,0x2100000003007fe40000,0x70080d30000000d0080)),
((563504390078464,0x81680000000100815e,0x500821c00000010,0x82c70000000800826c00,0x70082d20000000100,0xb8000000060083550000,0xa0083c1000000010083,844993258323968),(0x854700000010008491,0x60085bd00000005,0x86410000000300860900,0x60086d90000000800,0xbb000000050087560000,0x3008826000000060087,0x4008876000000,0x8911000000080088be),(0x900897200000007,0x89f1000000010089e600,0x5008a980000000900,0x2800000007008adc0000,0xa008b8c00000007008b,0x4d1003b008bf1000000,0x931f05c1002d008f6d,0x2000939e00000007),(0x952d0000000100952100,0x160095750000000700,0xb30000000200968f0000,0x800984d000000180096,563605841903616,0x99b7000000150098ce,0x230099ea00000004,0x9d040000001f009bf600),(0x7009d110000000100,0x7700000002009d5b0000,0x1009edb00000012009d,0x5009ee8000000,0xa10e0000001a009f35,0xc00a17600000004,0xa1e90000000100a1de00,0x100a24d0000000800),(0x9c0000000600a2570000,0x100a3f30000001a00a2,0x600a400000000,0xa4c60000000700a483,0x700a4d200000001,0xa5460000000100a53b00,0x100a5950000000600,0x30000000500a5a40000),(0x100a6790000000b00a6,0x600a685000000,0xa6fa0000000100a6f1,0x200a75500000007,0xa84b0000001000a77300,0x600a8580000000100,0xba0000000100a8ac0000,0x100a9070000000800a8),(0x700a914000000,0xa9900000000100a980,72244257611579396,0xaa270000000400a9ce00,0x1000aa700000000300,0x4c05d2004600aaeb0000,0x2400b0490000001d00ae,0x500b1bc000000)),
((0xb41d0000002d00b211,0x1800b46600000007,0xb5830000000100b57300,0x100b6190000000f00,0x7d0000000700b62a0000,0x2600b6cf0000000700b6,0x400b86b000000,0xba350000002c00b8af),(0x1500ba7d00000004,0xbb680000000100bb5500,0x200bb7c0000000100,0xbf0000000100bbaa0000,0x100bbc90000000100bb,282282095017984,0xbc0c0000000100bc00,72264405303164929),(0xbc3d0000000100bc3400,0x200bca00000000600,0xd70000000100bccd0000,0x100bdf90000000d00bc,0x500be1b000000,0xbe7e0000000100be6c,0x1000be8f00000001,0xc10f0000001300bfdd00),(0x300c1510000000500,0xe00c17d0000,0x100c3380000000c00c2,0x500c343000000,0xc3980000000100c38e,72275636642644020,0xc6a70000000500c65a00,0x100c6ba0000000100),(0xef0000000100c6cc0000,0x100c76e0000000700c6,282331856240640,0xc7b60000000100c793,0xa00c7c700000001,0xc87f0000000100c85800,0x1300c8ba0000000500,0xb40000000100c99b0000),(0x200c9f70000000400c9,7319217179197440,0xcb5e0000000700cb08,0x400cb6900000001,0xcb9c0000000100cb9100,0x200cbc50000000400,0x370000002300cbdc0000,0x200ce800000000900ce),(0x2400ce94000000,0xd0160000000800cfb7,72286670413627398,0xd0f30000000700d06500,0xd00d1040000000100,0xdc0000000400d1a00000,0x2200d1ef0000000200d1,282388915552256),(0xd85b072b005b00d4d9,0x400da3300000015,0xddb70808002f00da6500,0x100e0000000001200,0xb50000000d00e00c0000,0x1900e0df0000000200e0,0x800e321000000,0xe3950000000300e375)),
((72307969156448260,0xe3e70000000400e3c100,0xc00e3f40000000100,0x940000000100e4890000,0xa00e4db0000000600e4,282459832844288,0xe6030000000700e558,0x300e60d00000001),(0xe6540000000100e64a00,0xd00e67f0000000400,0x4e0000000100e7420000,0x700e7990000000600e7,0x500e7dc000000,0xe8280000000200e80b,0x1300e8d20000000d,0xea080000000400e9d100),(0x800ea310000000200,0x9c086c003200ea820000,0x2b00f1040922002e00ed,0x600f3dd000000,0xf6ca0000003c00f40a,0x2100f70100000005,0xf8470000000100f83900,0x1b00f8a80000000900),(0x990a3d003200f97c0000,0x160100360abb003e00fc,0x401027d000000,0x1052d0000002a0102b2,0xd0105cf00000010,0x6440000000101063400,0x10106a30000000b01,0xd70000000e0106ae0000),(0x1801082c000000060107,282615089201152,0x109dd0000000a010985,0x50fc00750b2300000012,0x19cfa62e88589e05a0ee,0x5f429e5761e0f8908644,0x9d13c29cda3659d13c5f,0xcac5bc8fc7255702f569),(0xbae7efd46e05748cc85f,0x332f5c62a13be3f0069,0x6723b6e33e20592f513e,0x337c62b927bc34d002fb,0x9bae5a8da8c75b1b88cb,0x37c1517f04d001edf009,0x72faec08b636d590e4b3,0xedd0ad8a4cc0878064dd),(0x7bcd9bef5797d304f162,0xd38e18d567b1ff48f7,0x3ee3bc3549aec08f1ffa,0xf61dc49083206b95b36e,0xf5b6112e043ca79a3593,0xc7caadfb165622fbd6fc,0xd7710efa311eff535647,0x105d6ac3297edb1aa5a5),(0xc96219f04685f9744ce3,0xcbd99a18487eab2f6f7f,0x40a2f4e5ee93343097b4,0x2bd80502f600c0bd8010,0x2cc9880b325a02cc948,0x2cfe20df260df220df1a,0x1348b20020c2ca59fdc1,0xe09de8960f4f3b092c40)))

def page22 : WordPage :=
(((0xf610980cf6272fe9d626,0x268cdb5de00d3624f813,0x88d19bdf81e48428032d,0x9c8024cea09830050955,0xadb54bcb86801a000000,0x59f959b771d2f32199ad,0x1677700001bb3f260006,0xb8fe98e309c0f382c855),(0xa7f3cd415df2cfa80075,0x8b48843a1aac0bd00680,0x1d1e0f9cbfd1ed5ce2de,0x9fa83d933b0ba3e1d9cc,0x851b20ee8a519037423d,0x6b6a427d596e8183300e,0x6ae3f400122191b77500,0xd921675c7a0d96ceac11),(0xf66cb6b1ca2dd9e4511e,0x9310f84289e748efefd1,0x728e87f807d30fa347d2,0x210daf7cb97e79a81bd6,0x9bc458edbd7398101867,0x4acdbd968043b6ae4008,0xa2fa440b1604891e2cd,0x6d5c730d550e7920f01f),(0x44b385400a039e7bf02b,0x7111bec22c001092d255,0x1fb6ee8518be6490e00d,0x757ba4405dd67428cc4,0x40eec9cee14e33408b27,0xc4bffe218b286336e2c6,0x620c6ff8812e1f42b10e,0xa751faa5c35a58817185),(0xfd49e7d32165336d5ace,0x493b5e16719cf57619c1,0xbb40665521700b2a9c7,0x791424197330bf0f2fe3,0xc0b0a70156eb59ac097d,0xccc58e09aa4f27823386,0xfb2582a6e8ea0de503d8,0xb875db4b6eb5e66bc812),(0x2e19985f879aafcf3a9c,0xf4e546f5fe559adadc95,0x4b6eb59ac0d2bec97e79,0x3ac9adac5ad3e52e29db,0x410bca440b500218d3d0,0x75f69116ebff90f56cfb,0xacf73b0bd6e81575d53,0xe0da713e98f71cfb87c1),(0xa705035f8d0d331ffa7e,0xd259b6ad6753a8c17653,0x307676394042a7c10a18,0x2b83a54aba939ef464bd,0x8563fcccb3062e3f404,0xdb210a4ffe8e08503e8e,0x6107ecb80588dbd24f03,0x22f1c2030cf9939d70b1),(0xd7e048849da7cadcb04,0x47943d57a0bebec6be92,0x8fad0ffd83cb1a5ef685,0x4bc714b4468bdb492e1e,0xaad708956634830b0196,0xc6f22365a0119c5a4b31,0xd3fc00e113c6a5a8c47b,0xf4a7b5a322d09697d5c1)),
((0xc3116acd6d6436a76cdb,0x5c2bc277d9af94dd6022,0xf9d07b5b966355ae1122,0xa89e1962d7a05780d3f7,0xfd587d9d5f182897ae33,0x38bc135e8d6b1d7116b7,0x75c45adfea303077a1cb,0x5bf1e27d69c219fdb5ac),(0x1778b569ee5150f846b,0x67428d857c2443b7fa5e,0xf721e1f11b181996ad34,0x83db3266bfcde83da99f,0x23f4d2ed30f0a339adfe,0x1796a946ff7ef4b976f1,0x29998af01499e3e7d18,0xc0c33c19841d7813489d),(0xadf6b87096f66dea3487,0x165f21541ba763f41b81,0x92ac1723e14bbd390046,0x9f136e321c610ea3c991,0xf6a72c4e50eaa8842dd5,0x5b36c836dd7dffb9f9e0,0x2095a19b3047e09ca62d,0xb1e5034943faa27527ff),(0x94d93a84cfb8f2a0096e,0x1fbf39f40e2a97e16523,0x83233cc34be382c426fd,0x99d200abe2c443adf857,0xe8cf0a3171a25e4de5b7,0xfc5363159434981a2adf,0x299b609006ff46bfbac8,0x74e33b79d022c5224927),(0x4fa9c91813118865960b,0xb3a794f3e4db561f674a,0x9f23ce90595ef35c88f,0x8c11a826d2dbcf68d853,0x48a9114eb081601c91a8,0x53777c0eec9a6349b4be,0xf26f1fe29525ba9d8df0,0xe1e7c1ddb9c3f2269c70),(0xd28645ac57d77d5d3e69,0xbbfa1aa5c3bbf35672aa,0xb5f178043b3ab755ff8d,0xe0366d5152e2ec0f753,0xd1276bb2d759fc0072d,0xf1deb5a00804720104c0,0xe019acdd68346ac6ada0,0x8a5b5a954031db8291ff),(0xc6b5cb0222c082602c4a,0x3f397a03bdcd0006823,0xe20c61f4000000e917e8,0x8e776d1e7fd079341843,0xc8e5b4c2f582ee300559,0x58ab9dd9b71ef636dc59,0xf5efadf21da85c3e2b5b,0xe7b46c0dff71f3085591),(0x766dab14537b3b00f46d,0x3d1a449c6bb02dc1e828,0x6dc7bcf6778f1e88089e,0xc566dc7bcdf7e5173a56,0x4c08e59848f8b3efcb73,0x6264d2519ddde7c07823,0x7f1e30b5533d086eb2cc,0xb043efdd1a49e7ca7bb1)),
((0x7528ec409e6631d2d12,0x17e15c2245accbdff1bf,0xfb95ed202f62fc112290,0xdfaf7fe8327b632f2e5e,0x3850c0eff4930055eff8,0xc77aed8c458478bee1f5,0xa42a59cbc34b43fc22c7,0x4cc9ba261e1a17291aa),(0xbad05c8d82acaf660c3e,0x7d58103dfdbfaeea21ac,0x899e46d5e3f1611e2fb8,0xaa90a9657b2d2c4ae947,0xf813326e89878685ca46,0x234ba172360ab2bd9830,0xa89a3c11ac1e6f1bf1fb,0xdbc5691100ebcdb8d586),(0x3ece0f7f1b17c02d6f2c,0x582bf6cd4adbab3b194f,0xf7bfe37e0a1524e78518,0xeb060dad870849391252,0x2c9f3d16a6091fc4ad4b,0x69a34c77bfe37e309217,0xc55222e11ac74bb8c6ff,0xf2eba2670bcde36938b4),(0x21d804527191bfc0ec69,0x2340e5d7afc242fb6ef9,0xfeb716b45901dfb9aef6,0xb8b0a2657245c7453346,0xe9d27b9c7a86f50dcc49,0xc1a9a40aba8228c3dc28,0x939496a8406ed1013b49,0xafc8d65d700af2cec0e),(0x5e7046732b4a8a865447,0x4c887ebc4efbf6ad0769,0xa46a589a8dc5f9e1551e,0xa75f1054bd30a304b8cf,0x233f68c57da762770587,0xe6af36eae42ae68d1da,0x4e06cf2e499c46d1deba,0xd0e71e82d61db9a78074),(0x26fd18adffb331cacafe,0x44fd4010ae41a292ea4b,0xa484581ff416f533cfda,0xd2cd27b5bfd63040b0c3,0x6851403d258df9e1e4c1,0x5ac1e14a068bda39a27,0x8c4d2ebb768e744a5ad,0xd28ddfbaf33895711ae0),(0x81002d6c5ccbe9b94455,0x5cd224e1e509bbcbee7a,0x8ee2289ef176e302d2d,0xa1ac714faf4ce261039b,0x9a7f7afb5f271dcac222,0xbb3ba77abe0b6f4c206b,0xdc5fcae55e8a9068d6d1,0x453a095a28299e07d6b6),(0x16b2c129f11f098b7843,0x7d1015ec35c010ec6b6b,0xb8058c7c7729961e0f6a,0x25226a6835dd547ac1f6,0x2dfdc2489a9a0cd13b27,0x74c3d798ad96e34e5b3c,0xd98e3f0a64d72336eeda,0xda2a9ab31f99847b58a)),
((0xf48816ace86a8374bea6,0x766a3e6ee5f715b911e5,0x88cbf735b911eb54118,0xdaf5a24111d4f8a364a,0x1123a7712d1783ec21,0xbac05f4c54c9d46d9689,0x4a2b318f53b52a1cc504,0x2a3fc625ccd5a90b90c),(0xb999b177ee43a4e14cc0,0x52cda2e39dac97973c8b,0x2a657749324bce36a562,0xf078eaaa9529733d6243,0xcbca02243e10a23efd50,0x2c4639daa9a40967802,0xcc0ed51c320899b6161d,0x1118e61ba29988d1831d),(0x2cab290a25f010ead51,0x83864e96615901e0107,0xf20d05321b6ef9bf9af0,0x68270134d81825348bd1,0xbd8b77fa9a2dbea38a90,0x71a8c63afef57d5ca668,0x6997eff8610eabefc11a,0xa1a535d62f5caf408b17),(0x6b7cf128adfd71cd4252,0x202845d6c1460b734bc,0x65c1a38e4c649c93926b,0xae4eb002d9001a1a8,0x2553b99f470086074282,0xb32103ac520d52d82c07,0xf40b870e44abb11ec3ab,0x34bfc172025c8f797d33),(0x508ba72bbeec4d41a73,0x3b22e49c93c24927b82,0xf5029b575da86075a596,0xe013f87c55302a98007e,0xa265ce432e4d40015c86,0x717f1100d76026d740a0,0x5f5bfd4752041885d797,0xdec3f4c4a6f2148dc497),(0xfa89a9515ea95ef421ea,0x75af65875d7d0357ca97,0x35b5a7cb9e3bf7d9e391,0x6ad5fc591cd2f8f494b,0xb7b2d0186141315164a5,0x26a69c2c3c1ec58571d9,0x224e3534d761e19620e1,0x23eeb4c2b7a28fa91fad),(0xec4483ed89194a1fa855,0xcf51211b1a184f979ec2,0xec432bd6d0b67fe9f534,0xd93a9a6e30f0a316a69a,0xe76cdc8d7a0f00b33ddf,0x114ee10ac10cef87fe9,0x69175ed13da511dbf749,0xe2f65036e829697eb467),(0xf353c75efa384060db36,0x2103d2b94f239f3e6e9c,0x961c6845b16600871b66,0x11700b1600d916f26479,0x84f0b9f821d8dbd330cd,0xbcb824453d8cf0a511e6,0x990910990910990911e,0x29031029031029099091)),
((0x90b11390b10310290310,0xa90a11390b11390b113,0x690a90a10a90a10a90a1,0x90690790690790690790,0x2b91892b91892b918907,0xf38108088000eb2b9189,0x90110190118288208180,0x5a04901901101901101),(0x3106204905a049062049,0x10310410310410310410,0xa30ba0db05307b0ba04,0x2284002a03b02221b073,0x800100a00185002a8480,0x6205985800100a00183,0x4114a05906205914a059,0x10410510410510410510),(0x11b1ca12306b0e31ca05,0x3986803904b03919b0b3,0x300b0230128780398700,0xa200288001b02b01203,0x690aa00a0a20020aa00a,0x10690910690910690910,0x5a0b10620b105a0b109,0x1b0830230330130620b1),(0x9a07308a8a002b03b0,0x990818a809a89808a89,0x5a099081099081099081,0x207207a05a0a207207a0,0x120a901a0a90120a90a,0x906100906100901a0a9,0xa0390520390610090610,0x330b20ba0390520390b),(0x38d802b0430b206b023,0x8d08c808b8c00938b80,0x4d085b0043002f00628e,0xc700010056004a004b00,0x700c800130005000300,512,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0)),
((0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0)),
((0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0)),
((0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0),(0,0,0,0,0,0,0,0)))

def wordPage (i : Nat) : WordPage :=
  (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then page0 else page1) else (if i < 3 then page2 else (if i < 4 then page3 else page4))) else (if i < 8 then (if i < 6 then page5 else (if i < 7 then page6 else page7)) else (if i < 9 then page8 else (if i < 10 then page9 else page10)))) else (if i < 17 then (if i < 14 then (if i < 12 then page11 else (if i < 13 then page12 else page13)) else (if i < 15 then page14 else (if i < 16 then page15 else page16))) else (if i < 20 then (if i < 18 then page17 else (if i < 19 then page18 else page19)) else (if i < 21 then page20 else (if i < 22 then page21 else page22)))))

def dataWord (i : Nat) : Nat :=
  strict i fun j =>
  if j < 11558 then
    let outer := wordPage (j >>> 9)
    let middle := memberOfEight ((j >>> 6) &&& 7) outer
    let inner := memberOfEight ((j >>> 3) &&& 7) middle
    memberOfEight (j &&& 7) inner
  else 0

def directFamilyAt : Nat := 0
def directSegmentsAt : Nat := 198
def directFeaturesAt : Nat := 3874
def directNumbersAt : Nat := 5215
def paletteFamilyAt : Nat := 12253
def paletteRefAt : Nat := 12847
def paletteRecordAt : Nat := 15707
def paletteOrdinalAt : Nat := 18896
def cdfAt : Nat := 35971
def distributionsAt : Nat := 39378
def proofsAt : Nat := 39686
def casesAt : Nat := 107958
def blocksAt : Nat := 109344
def claimsAt : Nat := 112354
def claimWordsAt : Nat := 115181
def claimSpecialsAt : Nat := 115541
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
  let v := id / 2
  let (shape,origin) := region v
  let coord := v-origin
  let family := 2*shape+id % 2
  strict (little (paletteFamilyAt+9*family) 9) fun row =>
  let ref := row &&& 65535
  let record := (row >>> 16) &&& 65535
  let ordinals := (row >>> 32) &&& 524287
  let rw := (row >>> 51) &&& 15
  let lw := (row >>> 55) &&& 7
  let ow := (row >>> 58) &&& 15
  let sw := (row >>> 62) &&& 15
  strict (bitWindow (8*paletteRefAt+ref+rw*(coord/8)) rw) fun index =>
  strict (bitWindow (8*paletteRecordAt+record+(lw+ow)*index) (lw+ow)) fun info =>
  (family,coord,info &&& ((1 <<< lw)-1),8*paletteOrdinalAt+ordinals+sw*(info >>> lw),sw)

def optionAt (m : Menu) (i : Nat) : Nat :=
  let (family,coord,count,first,width) := m
  if i ≥ count then 2 else templateAt family coord (bitWindow (first+width*i) width)

def optionCount (m : Menu) : Nat := m.2.2.1

def applyMenu {α : Type} (m : Menu) (use : Menu → α) : α :=
  match m with
  | (family,coord,count,first,width) =>
    strict count fun count => strict first fun first => strict width fun width =>
    use (family,coord,count,first,width)

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

inductive Obligation (db : Nat → Clause) where
  | need (fact : Lit)
  | finish (fact : Lit) (reason : Nat) (clause : Clause) (same : clause = db reason)

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

def needs {db : Nat → Clause} (p : Lit) (c : Clause) : List (Obligation db) :=
  (c.filter fun l => l != p).map fun l => .need (opposite l)

def walk {α : Type} (db : Nat → Clause) (pick : Picker α) :
    Nat → Trail α → List (Obligation db) → Option (Trail α)
  | _,s,[] => some s
  | 0,_,_ :: _ => none
  | fuel+1,s,.need p :: tail =>
    if s.conditional.testBit (tag p) then walk db pick fuel s tail
    else match pick s.permanent s.conditional p s.stream with
      | none => none
      | some (none,more) => walk db pick fuel (s.assume p more) tail
      | some (some reason,more) =>
        let clause := db reason.1
        let finish := .finish p reason.1 clause rfl :: tail
        let next := if reason.2 then finish else needs p clause ++ finish
        walk db pick fuel {s with stream := more} next
  | fuel+1,s,.finish p _ clause _ :: tail =>
    if allFalseExcept s.permanent (some p) clause then
      walk db pick fuel (s.assertPermanent p) tail
    else if allFalseExcept s.conditional (some p) clause then
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
      | finish p key clause eq =>
        subst clause
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

def chooseReason (source : Nat → Clause) (enabled : Nat → Bool) (n : Nat) (prior : List Clause)
    (_root conditional : Nat) (p : Lit) (s : State) : Option (Option (Nat × Bool) × State) :=
  let id := tag p
  applyMenu (menuFor id) fun m =>
  match firstForced source enabled conditional p m 4 0 2 with
  | some a => some (some (2*(a-3),true),s)
  | none =>
    let size := optionCount m
    let shift := 24*(((id*1103515245+12345) >>> 11) % 512)
    let old := if cacheOn then (s.2 >>> shift) &&& 16777215 else 0
    let reuse := cacheOn && size>1 && old/128==id+1
    let (value,after) := rankOrOnly byte interval size (2*((size-1)/3)+reuse.toNat) s.1
    let rank := if reuse then if value=0 then old % 128 else if value-1 < old % 128 then value-1 else value else value
    let saved := if cacheOn && size>1 then s.2 ^^^ ((old ^^^ ((id+1)*128+rank)) <<< shift) else s.2
    strict after fun after => strict saved fun saved =>
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
    (enabled : Nat → Bool) (start : Nat → State) (length : Nat → Nat) (published : Nat → Claims)
    (last : Nat) (checked : ∀ j ≤ last,
      segment source (chooseReason source enabled) packet 500000 (length j) 0 (previous published j).length
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
  segment source (chooseReason source enabled) packet 500000 (lengthOf b) 0 prior.length 0 prior
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
    apply complete hs enabled (fun j => startOf (firstBlock cell+j)) (fun j => lengthOf (firstBlock cell+j))
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
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PreparedCircuit.Reindex

def wire {n m : ℕ} (σ : Fin n → Fin m) (i : ℕ) : ℕ :=
  if hi : i < n then (σ ⟨i, hi⟩).val else m + (i - n)

def gate {n m : ℕ} (σ : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire σ)⟩

def circuit {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate σ), wire σ C.output⟩

theorem size_eq {n m} (σ : Fin n → Fin m) (C : Circuit) : (circuit σ C).size = C.size := by
  simp [circuit, Circuit.size]

private theorem readWire {n m} (σ : Fin n → Fin m) (x : Fin m → Bool) (gates : List Bool) (i : ℕ) :
    (List.ofFn x ++ gates).getD (wire σ i) false =
      (List.ofFn (fun j => x (σ j)) ++ gates).getD i false := by
  by_cases hi : i < n
  · let j := σ ⟨i, hi⟩
    have left : j.val < (List.ofFn x).length := by simp
    have right : i < (List.ofFn (fun k => x (σ k))).length := by simpa using hi
    simp only [wire, hi, ↓reduceDIte]
    rw [List.getD_append _ _ _ _ left, List.getD_append _ _ _ _ right]
    simp [List.getD_eq_getElem?_getD, hi, j]
  · have left : (List.ofFn x).length ≤ m + (i - n) := by simp
    have right : (List.ofFn (fun k => x (σ k))).length ≤ i := by simpa using Nat.le_of_not_gt hi
    simp only [wire, hi, ↓reduceDIte]
    rw [List.getD_append_right _ _ _ _ left, List.getD_append_right _ _ _ _ right]
    simp

private def appendValue (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldGates {n m} (σ : Fin n → Fin m) (x : Fin m → Bool) (gs : List Gate)
    (priorValues : List Bool) : ∃ suffix : List Bool,
      (gs.map (gate σ)).foldl appendValue (List.ofFn x ++ priorValues) = List.ofFn x ++ suffix ∧
      gs.foldl appendValue (List.ofFn (fun j => x (σ j)) ++ priorValues) = List.ofFn (fun j => x (σ j)) ++ suffix := by
  induction gs generalizing priorValues with
  | nil => exact ⟨priorValues, rfl, rfl⟩
  | cons g gs ih =>
    let w := List.ofFn (fun j => x (σ j)) ++ priorValues
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have inputs : (gate σ g).inputs.map (fun i => (List.ofFn x ++ priorValues).getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      simp only [gate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact readWire σ x priorValues i
    have left : appendValue (List.ofFn x ++ priorValues) (gate σ g) = List.ofFn x ++ (priorValues ++ [v]) := by
      unfold appendValue
      rw [inputs]
      exact List.append_assoc _ _ _
    have right : appendValue w g = List.ofFn (fun j => x (σ j)) ++ (priorValues ++ [v]) :=
      List.append_assoc _ _ _
    obtain ⟨suffix, hl, hr⟩ := ih (priorValues ++ [v])
    refine ⟨suffix, ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons, left]
      exact hl
    · change gs.foldl appendValue (appendValue w g) = _
      rw [right]
      exact hr

theorem reindexed_wires {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    ∃ tail, (circuit σ C).wires (List.ofFn x) = List.ofFn x ++ tail ∧
      C.wires (List.ofFn fun j => x (σ j)) = (List.ofFn fun j => x (σ j)) ++ tail := by
  obtain ⟨tail, left, right⟩ := foldGates σ x C.gates []
  refine ⟨tail, ?_, ?_⟩
  · change (C.gates.map (gate σ)).foldl appendValue (List.ofFn x) = _
    simpa only [List.append_nil] using left
  · change C.gates.foldl appendValue (List.ofFn fun j => x (σ j)) = _
    simpa only [List.append_nil] using right

theorem eval_with_tail {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) (tail : List Bool) :
    (circuit σ C).eval (List.ofFn x ++ tail) = C.eval ((List.ofFn fun j => x (σ j)) ++ tail) := by
  obtain ⟨suffix, left, right⟩ := foldGates σ x C.gates tail
  change ((C.gates.map (gate σ)).foldl appendValue (List.ofFn x ++ tail)).getD (wire σ C.output) false =
    (C.gates.foldl appendValue ((List.ofFn fun j => x (σ j)) ++ tail)).getD C.output false
  rw [left, right]
  exact readWire σ x suffix C.output

theorem read_with_tail {n m : ℕ} (σ : Fin n → Fin m) (x : Fin m → Bool) (tail : List Bool) (i : ℕ) :
    (List.ofFn x ++ tail).getD (wire σ i) false = ((List.ofFn fun j => x (σ j)) ++ tail).getD i false :=
  readWire σ x tail i

end PreparedCircuit.Reindex

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

end PriorG11.Join

namespace PriorG11.Splice
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PreparedCircuit.Reindex

theorem reindex_after {n m : ℕ} (σ : Fin n → Fin m) (before : ℕ) {T : Circuit}
    (hT : IsAO2 (n + before) T) : IsAO2 (m + before) (circuit σ T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
    exact hT.1 k hk
  · intro j hj i hi
    have hj' : j < T.gates.length := by simpa [circuit] using hj
    have he : gateAt (circuit σ T) j = gate σ (gateAt T j) := by
      simp [gateAt, circuit, List.getD_eq_getElem?_getD, hj']
    rw [he] at hi
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    have h := hT.2.1 j hj' w hw
    by_cases low : w < n
    · simp only [wire, low, ↓reduceDIte]
      have bound := (σ ⟨w,low⟩).isLt
      omega
    · simp only [wire, low, ↓reduceDIte]
      omega
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    simpa [gate] using hT.2.2 k hk

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

theorem append_wires (P T : Circuit) (w : List Bool) :
    (Join.append P T).wires w = T.wires (P.wires w) := by
  simp only [Join.append, Circuit.wires, List.foldl_append]

def assembled {n : ℕ} (p : Fin (n+1)) (P T : Circuit) (conj : Bool) : Circuit :=
  let lifted := circuit p.succAbove P
  let test := root (n+1+P.size) conj p.val (wire p.succAbove P.output)
  Join.append (Join.append lifted test) (circuit p.succAbove T)

theorem assembled_size {n : ℕ} (p : Fin (n+1)) (P T : Circuit) (conj : Bool) :
    (assembled p P T conj).size = P.size + 1 + T.size := by
  simp only [assembled, Join.append_size, size_eq]
  rfl

theorem assembled_legal {n : ℕ} (p : Fin (n+1)) {P T : Circuit} (conj : Bool)
    (hp : IsAO2 n P) (ht : IsAO2 (n+1+P.size) T) (out : P.output < n+P.size) :
    IsAO2 (n+1) (assembled p P T conj) := by
  have hp' : IsAO2 (n+1) (circuit p.succAbove P) := by
    simpa using reindex_after p.succAbove 0 hp
  have ow : wire p.succAbove P.output < n+1+P.size := by
    by_cases h : P.output < n
    · simp only [wire, h, ↓reduceDIte]
      have s := (p.succAbove ⟨P.output,h⟩).isLt
      omega
    · simp only [wire, h, ↓reduceDIte]
      omega
  let test := root (n+1+P.size) conj p.val (wire p.succAbove P.output)
  have legal : IsAO2 (n+1+(circuit p.succAbove P).size) test := by
    rw [size_eq]
    exact root_legal conj (by have h := p.isLt; omega) ow
  apply Join.append_legal (Join.append_legal hp' legal)
  rw [Join.append_size, size_eq]
  have one : test.size = 1 := rfl
  rw [one]
  have h : IsAO2 (n+(P.size+1)) T := by convert ht using 1 <;> omega
  exact reindex_after p.succAbove (P.size+1) h

theorem assembled_eval {n : ℕ} (p : Fin (n+1)) (P T : Circuit) (conj : Bool) (y : Fin (n+1) → Bool) :
    (assembled p P T conj).eval (List.ofFn y) =
      T.eval (P.wires (List.ofFn fun j => y (p.succAbove j)) ++
        [combine conj (y p) (P.eval (List.ofFn fun j => y (p.succAbove j)))]) := by
  let x := fun j => y (p.succAbove j)
  obtain ⟨tail,large,small⟩ := reindexed_wires p.succAbove P y
  have left : (List.ofFn y ++ tail).getD p.val false = y p := by
    rw [List.getD_append _ _ _ _ (by simpa using p.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, p.isLt, ↓reduceDIte, Option.getD_some]
  have right : (List.ofFn y ++ tail).getD (wire p.succAbove P.output) false = P.eval (List.ofFn x) := by
    change _ = (P.wires (List.ofFn x)).getD P.output false
    rw [small]
    exact read_with_tail p.succAbove y tail P.output
  let value := combine conj (y p) (P.eval (List.ofFn x))
  have test : (root (n+1+P.size) conj p.val (wire p.succAbove P.output)).wires (List.ofFn y ++ tail) =
      (List.ofFn y ++ tail) ++ [value] := by
    change (List.ofFn y ++ tail) ++ [(op conj).eval [(List.ofFn y ++ tail).getD p.val false,
      (List.ofFn y ++ tail).getD (wire p.succAbove P.output) false]] = _
    rw [left, right, op_eval]
  rw [assembled, Join.append_eval, append_wires, large, test, List.append_assoc,
      eval_with_tail, ← List.append_assoc, ← small]

theorem exists_mismatch {n bound : ℕ} (p : Fin (n+1)) (P T : Circuit) (conj : Bool)
    (f : (Fin (n+1) → Bool) → Bool)
    (lower : ∀ C : Circuit, IsAO2 (n+1) C → (∀ y, C.eval (List.ofFn y) = f y) → bound ≤ C.size)
    (hp : IsAO2 n P) (ht : IsAO2 (n+1+P.size) T) (out : P.output < n+P.size)
    (room : P.size+T.size+1 < bound) :
    ∃ x : Fin n → Bool, ∃ b : Bool,
      T.eval (P.wires (List.ofFn x) ++ [combine conj b (P.eval (List.ofFn x))]) ≠ f (p.insertNth b x) := by
  by_contra! agrees
  let C := assembled p P T conj
  have same (y : Fin (n+1) → Bool) : C.eval (List.ofFn y) = f y := by
    rw [show C = assembled p P T conj from rfl, assembled_eval]
    have recover : p.insertNth (y p) (fun j => y (p.succAbove j)) = y :=
      Fin.insertNth_eq_iff.mpr ⟨rfl,rfl⟩
    simpa only [recover] using agrees (fun j => y (p.succAbove j)) (y p)
  have h := lower C (assembled_legal p conj hp ht out) same
  change bound ≤ (assembled p P T conj).size at h
  rw [assembled_size] at h
  omega

end PriorG11.Splice

end PEqualNP.Outside.L_meta_18015

open PEqualNP.Outside.L_meta_18015.PriorG11 in
theorem PEqualNP.Outside.L_meta_18015 : ∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →       PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →         x3.size + x4.size ≤ (17 : ℕ) →           (9 : ℕ) ≤ x3.output →             x3.output < (9 : ℕ) + x3.size →               have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>                 have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));               (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.false) → ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x14 || x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13) := by
  intro v p P T hv hp ht room _ out _ _
  let f := fun y : Fin 10 → Bool => Bounds.packed (v.insertNth false y)
  have lower (C) := Bounds.packed_lower
    (Proof.certified Proof.successful) v C hv
  exact Splice.exists_mismatch (n := 9) (bound := 19) p P T false f
    lower hp ht out (by omega)
