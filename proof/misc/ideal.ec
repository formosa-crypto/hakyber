(* -------------------------------------------------------------------- *)
(* Ideals                                                               *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List Ring StdRing Binomial.
require (*--*) Bigalg.

clone include Ring.ComRing.

clone import Bigalg.BigComRing with
  type t <- t,
  pred CR.unit   <- Top.unit,
    op CR.zeror  <- Top.zeror,
    op CR.oner   <- Top.oner,
    op CR.( + )  <- Top.( + ),
    op CR.([-])  <- Top.([-]),
    op CR.( * )  <- Top.( * ),
    op CR.invr   <- Top.invr,
    op CR.intmul <- Top.intmul,
    op CR.ofint  <- Top.ofint,
    op CR.exp    <- Top.exp

    proof CR.*

    remove abbrev CR.(-)
    remove abbrev CR.(/).

realize CR.addrA      by apply Top.addrA    .
realize CR.addrC      by apply Top.addrC    .
realize CR.add0r      by apply Top.add0r    .
realize CR.addNr      by apply Top.addNr    .
realize CR.oner_neq0  by apply Top.oner_neq0.
realize CR.mulrA      by apply Top.mulrA    .
realize CR.mulrC      by apply Top.mulrC    .
realize CR.mul1r      by apply Top.mul1r    .
realize CR.mulrDl     by apply Top.mulrDl   .
realize CR.mulVr      by apply Top.mulVr    .
realize CR.unitP      by apply Top.unitP    .
realize CR.unitout    by apply Top.unitout  .

import BAdd.

instance ring with t
  op rzero = Top.zeror
  op rone  = Top.oner
  op add   = Top.( + )
  op opp   = Top.([-])
  op mul   = Top.( * )
  op expr  = Top.exp

  proof oner_neq0 by apply/oner_neq0
  proof addr0     by apply/addr0
  proof addrA     by apply/addrA
  proof addrC     by apply/addrC
  proof addrN     by apply/addrN
  proof mulr1     by apply/mulr1
  proof mulrA     by apply/mulrA
  proof mulrC     by apply/mulrC
  proof mulrDl    by apply/mulrDl
  proof expr0     by apply/expr0
  proof exprS     by apply/exprS.

(* -------------------------------------------------------------------- *)
(*These should be somewhere near the Prelude*)
op pairify ( f : 'a -> 'b -> 'c ) : ('a * 'b) -> 'c =
fun z => f (fst z) (snd z).
op appsnd ( f : 'b -> 'c ) ( p : 'a * 'b ) : ('a * 'c) = (fst p, f (snd p)).
(* -------------------------------------------------------------------- *)
lemma binomial (x y : t) n : 0 <= n => exp (x + y) n =
  BAdd.bigi predT (fun i => intmul (exp x i * exp y (n - i)) (bin n i)) 0 (n + 1).
proof.
elim: n => [|i ge0_i ih].
+ by rewrite BAdd.big_int1 /= !expr0 mul1r bin0 // mulr1z.
rewrite exprS // ih /= mulrDl 2!BAdd.mulr_sumr.
rewrite (BAdd.big_addn 1 _ (-1)) /= (BAdd.big_int_recr (i+1)) 1:/# /=.
pose s1 := BAdd.bigi _ _ _ _; rewrite binn // mulr1z.
rewrite !expr0 mulr1 -exprS // addrAC.
apply: eq_sym; rewrite (BAdd.big_int_recr (i+1)) 1:/# /=.
rewrite binn 1:/# mulr1z !expr0 mulr1; congr.
apply: eq_sym; rewrite (BAdd.big_int_recl _ 0) //=.
rewrite bin0 // mulr1z !expr0 mul1r -exprS // addrCA addrC; apply: eq_sym.
rewrite (BAdd.big_int_recl _ 0) //= bin0 1:/# mulr1z !expr0 mul1r addrC.
congr; apply: eq_sym; rewrite /s1 => {s1}.
rewrite !(BAdd.big_addn 1 _ (-1)) /= -BAdd.big_split /=.
rewrite !BAdd.big_seq &(BAdd.eq_bigr) => /= j /mem_range rg_j.
rewrite mulrnAr ?ge0_bin mulrA -exprS 1:/# /= addrC.
rewrite mulrnAr ?ge0_bin mulrCA -exprS 1:/#.
rewrite IntID.addrAC IntID.opprB IntID.addrA.
by rewrite -mulrDz; congr; rewrite (binSn i (j-1)) 1,2:/#.
qed.

(* -------------------------------------------------------------------- *)

(*Ideal*)
op ideal (i : t -> bool) : bool =
   (exists x : t , i x)
/\ (forall x y : t , i x => i y => i (x+y))
/\ (forall x y : t , i x => i (x * y)).

lemma idealP (i : t -> bool) :
    (exists x, i x)
 => (forall x y, i x => i y => i (x+y))
 => (forall x y, i x => i (x * y))
 => ideal i.
proof. by move=> *; do! split. qed.

lemma idealW (P : (t -> bool) -> bool) :
  (forall i,
        (exists x, i x)
     => (forall (x y : t), i x => i y => i (x+y))
     => (forall x y, i x => i (x * y))
     => P i)
  => forall i, ideal i => P i.
proof. by move=> ih i [? [??]]; apply: ih. qed.

(*The zero ideal*)
op id0 : t -> bool = pred1 zeror.

(*The whole ring ideal*)
op idT : t -> bool = predT.

(*Intersection of two ideals*)
op interId ( i j : t -> bool ) : t -> bool =
  predI i j.

(*Sum of two ideals*)
op sumId ( i j : t -> bool ) : t -> bool =
  fun z => exists (x y : t), (z = x + y) /\ i x /\ j y.

(*Quotient of two ideals*)
op quoId ( i j : t -> bool ) : t -> bool =
  fun x => (forall y , j y => i (x * y)).

(*Ideal generated by a subset*)
op genId ( i : t -> bool ) : t -> bool =
  fun (x : t) =>
    exists l : (t * t) list ,
         ( x = big predT (pairify ( * )) l )
      /\ ( forall z , mem l z => i z.`1).

(*Product of two ideals*)
op prodId ( i j : t -> bool ) : t -> bool =
  genId (fun z => exists (x y : t), (z = x * y) /\ i x /\ j y).

(*Radical of two ideals*)
op radId ( i : t -> bool ) : t -> bool =
  fun x => exists n : int , 0 <= n /\ i (exp x n).

(*Principal ideal*)
op principal ( i : t -> bool ) : bool =
  exists x : t , i = genId (pred1 x).

(*Finitely generated ideal*)
op finitelyGenerated ( i : t -> bool ) : bool =
  exists lx : t list , i = genId (mem lx).



(**************************)
(* Lemmas                 *)
(**************************)

(*elim/idealW=> i [x ix] /(_ _ _ ix ix).*)

(*Ideals are not empty*)
lemma existsxInId : forall i , ideal i => exists x , i x by elim / idealW => i [x ix] _ _; exists x.

(*Ideals are stable by addition*)
lemma addi : forall i , ideal i => forall x y  , i x => i y => i (x+y) by elim / idealW.

(*Ideals are stable by opposite*)
lemma oppi : forall i , ideal i => forall x , i x => i (-x).
proof.
elim / idealW => i _ _ mulStab x ix.
rewrite - (mulr1 x) - mulrN.
by apply mulStab.
qed.

(*Ideals are stable by substraction*)
lemma subi : forall i , ideal i => forall x y , i x => i y => i (x-y).
move => i idi x y ix iy.
apply addi => //.
by apply oppi.
qed.

(*Ideals are stable by right multiplication by an element of the ring*)
lemma mulir : forall i , ideal i => forall x y  , i x => i (x * y) by elim / idealW.

(*Ideals are stable by left multiplication by an element of the ring*)
lemma mulri : forall i , ideal i => forall x y  , i y => i (x * y).
move => i idi x y iy.
rewrite mulrC.
by apply mulir.
qed.

(*Ideals are stable by integer multilplication*)
lemma muliz : forall i , ideal i => forall x n , i x => i (intmul x n).
move => i idi x n ix.
rewrite - mulr1 - mulrzAr.
by apply mulir.
qed.

(*zeror is in any ideal*)
lemma zeroInId : forall i , ideal i => i zeror.
elim / idealW => i [x ix] _ mulStab.
rewrite - (mulr0 x).
by apply mulStab.
qed.

(*A sum of elements of an ideal is in the ideal*)
lemma addi_big : forall i , ideal i => forall l , (forall x , mem l x => i x) => i (big predT idfun l).
move => i idi l il.
rewrite big_seq.
apply big_rec => /=.
+ by apply zeroInId.
+ move => x y ix iy.
  apply addi => //.
  by apply il.
qed.

(*A sum of x_i*y_i where x_i is in the ideal is in the ideal*)
(*Should be simplified once the proof that the radical is an ideal is simplified, using the previous lemma*)
lemma add_mulir_big : forall i , ideal i => forall l , ( forall (z : t * t) , mem l z => i z.`1) => i (big predT (pairify ( * )) l).
move => i idi l leftlIni.
rewrite big_seq.
apply big_rec.
+ by apply zeroInId.
+ move => [z1 z2] x zl ix.
  rewrite //=.
  apply addi => //.
  apply mulir => //.
  by apply (leftlIni (z1,z2)).
qed.

(*The zero ideal is an ideal*)
lemma id0IsId : ideal id0.
proof.
apply : idealP.
+ by exists zeror.
+ by move => x y @/id0 -> -> ; rewrite addr0.
+ by move => x y @/id0 -> ; rewrite mul0r.
qed.

(*The whole ring ideal is an ideal*)
lemma idTIsId : ideal idT by done.

(*The intersection of two ideals is an ideal*)
lemma interIdIsId : forall i j , ideal i => ideal j => ideal (interId i j).
move => i j idi idj.
apply : idealP.
+ exists zeror.
  by split ; apply zeroInId.
+ move => x y [ix jx] [iy jy].
  by split ; apply addi.
+ move => x y [ix jx].
  by split ; apply mulir.
qed.

(*The sum of two ideals is an ideal*)
lemma sumIsId : forall i j , ideal i => ideal j => ideal (sumId i j).
move => i j idi idj.
apply : idealP.
+ exists zeror zeror zeror.
  split.
  - by rewrite addr0.
  - by split ; rewrite zeroInId.
+ move => x y [xi xj [eqx [ixi jxj]]] [yi yj [eqy [iyi jyj]]].
  rewrite eqx eqy.
  exists (xi + yi) (xj + yj).
  split.
  - by ring.
  - by split ; apply addi.
+ move => x y [xi xj [eqx [ixi jxj]]].
  rewrite eqx mulrDl.
  exists (xi * y) (xj * y).
  by split => // ; split ; apply mulir.
qed.

(*The quotient of two ideals is an ideal*)
lemma quoIdIsId : forall i j , ideal i => ideal j => ideal (quoId i j).
move => i j idi idj.
apply : idealP.
+ exists zeror.
  move => x jx.
  rewrite mul0r.
  by apply zeroInId.
+ move => x y quox quoy z jz.
  rewrite mulrDl.
  by apply addi => // ; [apply quox | apply quoy].
+ move => x y quox z jz.
  rewrite - mulrA.
  apply quox.
  rewrite mulrC.
  by apply mulir.
qed.

(*The ideal generated by a subset of a ring is an ideal*)
lemma genIsId : forall i , ideal (genId i).
move => i.
apply : idealP.
+ by exists zeror [].
+ move => x y [lx [xEqSumlx unzip1Inilx]] [ly [yEqSumly unzip1Inily]].
  rewrite xEqSumlx yEqSumly.
  rewrite - big_cat.
  exists (lx ++ ly).
  split => //.
  move => z zInlxCatly.
  case : (mem_cat z lx ly) => zInlxOrly _.
  apply zInlxOrly in zInlxCatly.
  case : zInlxCatly.
  - by apply unzip1Inilx.
  - by apply unzip1Inily.
+ move => x y [lx [xEqSumlx unzip1Inilx]].
  rewrite xEqSumlx.
  rewrite mulr_suml.
  have eqfun : (fun (z : t * t) => z.`1 * z.`2 * y) = (pairify ( * )) \o (appsnd (transpose ( * ) y)) ; rewrite //=.
  - apply fun_ext.
    move => [z1 z2].
    rewrite /(\o) /pairify /appsnd /transpose /=. (*FIXME*)
    by rewrite mulrA.
  - rewrite eqfun.
    rewrite /big. (*FIXME*)
    rewrite map_comp filter_predT.
    rewrite - (filter_predT (map (appsnd (transpose ( * ) y)) lx)).
    exists (map (appsnd (transpose ( * ) y)) lx).
    split => //=.
    move => z zInMap.
    case : (mapP (appsnd (transpose ( * ) y)) lx z) => zP _.
    apply zP in zInMap.
    case zInMap => z' [z'Inlx eqz].
    rewrite eqz /appsnd /transpose /=. (*FIXME*)
    by apply unzip1Inilx.
qed.

(*The ideal generated by a set contains this set*)
lemma genIdContainsSet : forall i , forall x , i x => genId i x.
move => i x ix.
exists [(x,oner)].
split => //.
rewrite big_cons big_nil /predT /pairify=> //=. (*FIXME*)
by ring.
qed.

(*The ideal generated by a set is the smallest ideal containing this set*)
lemma genIdSmallestIdContainingSet : forall i j , ideal j => (forall x , i x => j x) => (forall x , genId i x => j x).
move => i j idj iIncj x [lx [eqx unzip1Inilx]].
rewrite eqx.
apply add_mulir_big => //.
move => z zInlx.
apply iIncj.
by apply unzip1Inilx.
qed.

(*The product of two ideals is an ideal*)
lemma prodIdIsId : forall i j , ideal i => ideal j => ideal (prodId i j).
move => i j idi idj.
rewrite /prodId. (*FIXME*)
by apply genIsId.
qed.

lemma exprM : forall x y n , 0 <= n => exp (x * y) n = (exp x n) * (exp y n). admitted.

(*The radical of an ideal is an ideal*)
lemma radIdIsId : forall i , ideal i => ideal (radId i).
move => i idi.
apply : idealP.
+ case : (existsxInId i idi) => x ix.
  exists x 1 => /=.
  by rewrite expr1.
+ move => x y [nx [le0nx iexnx]] [ny [le0ny ieyny]].
  exists (nx+ny).
  split ; [ apply addz_ge0 | rewrite binomial] => //.
  - by apply addz_ge0.
    (*This should be simpler*)
  - have eqf: (\o) idfun (fun (i0 : int) => intmul (exp x i0 * exp y (nx + ny - i0)) (bin (nx + ny) i0)) = (fun (i0 : int) => intmul (exp x i0 * exp y (nx + ny - i0)) (bin (nx + ny) i0)).
    rewrite /(\o) //=. (*FIXME*)
    rewrite - eqf.
    rewrite - big_mapT.
    apply addi_big => //.
    move => z zInl.
    case : (mapP (fun (i0 : int) => intmul (exp x i0 * exp y (nx + ny - i0)) (bin (nx + ny) i0)) (range 0 (nx + ny + 1)) z) => mapex _.
    apply mapex in zInl.
    case : zInl => r [_ eqz].
    rewrite eqz /=.
    apply muliz => //.
    case : (lez_total r nx) => ineqr.
    * apply mulri => //.
      rewrite - addzAC.
      by rewrite (exprD y (nx-r) ny)  // ; [rewrite subz_ge0 | apply mulri].
    * apply mulir => //.
      rewrite - (addzK (-nx) r) oppzK.
      by rewrite exprD // ; [rewrite subz_ge0 | apply mulri].
+ move => x y [n [le0n iexn]].
  exists n.
  split => //.
  rewrite exprM => //.
  by apply mulir.
qed.

(*A principal ideal is an ideal*)
lemma principalIdIsId : forall i , principal i => ideal i.
move => i [x eqi].
rewrite eqi.
by apply genIsId.
qed.

(*A finitely generated ideal is an ideal*)
lemma finitelyGeneratedIdIsId : forall i , finitelyGenerated i => ideal i.
move => i [lx eqi].
rewrite eqi.
by apply genIsId.
qed.

(*A principal ideal is finitely generated*)
lemma principalIsFinitelyGenerated : forall i , principal i => finitelyGenerated i.
move => i [x eqi].
exists [x].
by rewrite eqi.
qed.