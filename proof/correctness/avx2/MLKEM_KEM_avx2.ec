require import AllCore IntDiv List.
require import Jkem_avx2 MLKEM MLKEM_Poly MLKEM_PolyVec MLKEM_InnerPKE MLKEM_InnerPKE_avx2 MLKEMFCLib.
require import Array1152 Array32 Array960 Array1184 Array1088 Array64 Array128.
from Jasmin require import JModel.

import GFq Rq Sampling Serialization Symmetric VecMat InnerPKE MLKEM Fq Correctness.

import MLKEM_Poly.
import MLKEM_PolyVec.

axiom pkH_sha_avx2 mem _ptr inp: 
    phoare [Jkem_avx2.M(Jkem_avx2.Syscall)._isha3_256 :
          arg = (inp,W64.of_int _ptr,W64.of_int (3*384+32)) /\
          valid_ptr _ptr 1184 /\
          Glob.mem = mem
          ==> 
          Glob.mem = mem /\
          res = SHA3_256_1184_32
            (Array1152.init (fun k =>  mem.[_ptr+k]),
            (Array32.init (fun k => mem.[_ptr+1152+k])))] = 1%r.

axiom j_shake_avx2 mem _pout _pin1 _pin2: 
    phoare [Jkem_avx2.M(Jkem_avx2.Syscall)._shake256_1120_32  :
          arg = (W64.of_int _pout,W64.of_int _pin1,W64.of_int _pin2) /\
          valid_ptr _pout 32 /\
          valid_ptr _pin1 32 /\
          valid_ptr _pin2 1088 /\
          Glob.mem = mem
          ==> 
          touches Glob.mem mem _pout 32 /\
          (Array32.init (fun k =>  Glob.mem.[_pout+k])) = 
             SHAKE_256_1120_32 (Array32.init (fun k => mem.[_pin1+k])) 
                            (Array960.init (fun k => mem.[_pin2+k]), Array128.init (fun k => mem.[_pin2+960+k])) ] = 1%r.

axiom sha_g_avx2 buf inp: 
    phoare [Jkem_avx2.M(Jkem_avx2.Syscall)._sha3_512_64 :
          arg = (inp,buf)
          ==> 
          let bytes = SHA3_512_64_64 (Array32.init (fun k => buf.[k])) 
                                     (Array32.init (fun k => buf.[k+32])) in
          res = Array64.init (fun k => if k < 32 then bytes.`1.[k] else bytes.`2.[k-32])] = 1%r.


lemma pack_inj : injective W8u8.pack8_t by apply (can_inj W8u8.pack8_t W8u8.unpack8 W8u8.pack8K).

lemma mlkem_kem_correct_kg mem _pkp _skp  : 
   equiv [Jkem_avx2.M(Jkem_avx2.Syscall).__crypto_kem_keypair_jazz ~ MLKEM.kg_derand : 
       Glob.mem{1} = mem /\ to_uint pkp{1} = _pkp /\ to_uint skp{1} = _skp /\ 
        coins{2}.`1 = Array32.init(fun i => randomnessp{1}.[0 + i]) /\
        coins{2}.`2 = Array32.init(fun i => randomnessp{1}.[32 + i]) /\
       valid_disj_reg _pkp (384*3+32) _skp (384*3 + 384*3 + 32 + 32 + 32 + 32) 
        ==> 
       touches2 Glob.mem{1} mem _pkp (384*3+32) _skp (384*3 + 384*3 + 32 + 32 + 32+ 32) /\
       let (pk,sk) = res{2} in let (t,rho) = pk in
         sk.`1 = load_array1152 Glob.mem{1} _skp /\
         sk.`2.`1 = load_array1152 Glob.mem{1} (_skp + 1152) /\
         sk.`2.`2 = load_array32 Glob.mem{1} (_skp + 1152 + 1152) /\
         sk.`3 = load_array32 Glob.mem{1} (_skp + 1152 + 1152 + 32) /\
         sk.`4 = load_array32 Glob.mem{1} (_skp + 1152 + 1152 + 32 + 32) /\
         t = load_array1152 Glob.mem{1} _pkp  /\
         rho = load_array32 Glob.mem{1} (_pkp+1152)].
proc => /=.

swap {1} [3..5] 17.
swap {1} 1 14.

seq 19 4 : (
      z{2} = Array32.init(fun i => randomnessp{1}.[32 + i]) /\ 
      to_uint skp{1} = _skp +  1152 + 1152 + 32 + 32 /\
      valid_disj_reg _pkp (384*3+32) _skp (384*3 + 384*3 + 32 + 32 + 32 + 32) /\
      touches2 Glob.mem{1} mem _pkp (384 * 3 + 32) _skp (384*3 + 384*3 + 32 + 32 + 32 + 32) /\
      sk{2} = load_array1152 Glob.mem{1} _skp /\
      pk{2}.`1 = load_array1152 Glob.mem{1} (_skp + 1152) /\
      pk{2}.`2 = load_array32 Glob.mem{1} (_skp + 1152 + 1152) /\
      hpk{2} = load_array32 Glob.mem{1} (_skp + 1152 + 1152 + 32) /\
      pk{2}.`1 = load_array1152 Glob.mem{1} (_pkp) /\
      pk{2}.`2 = load_array32 Glob.mem{1} (_pkp + 1152)
); last first.
+ while {1} (aux{1} = 4 /\
       z{2} = Array32.init(fun i => randomnessp2{1}.[0 + i]) /\ 
       to_uint skp{1} = _skp +  1152 + 1152 + 32 + 32 + i{1}*8 /\
       valid_disj_reg _pkp (384*3+32) _skp (384*3 + 384*3 + 32 + 32 + 32 + 32) /\
       touches2 Glob.mem{1} mem _pkp (384 * 3 + 32) _skp (384*3 + 384*3 + 32 + 32 + 32 + 32) /\
       sk{2} = load_array1152 Glob.mem{1} _skp /\
       pk{2}.`1 = load_array1152 Glob.mem{1} (_skp + 1152) /\
       pk{2}.`2 = load_array32 Glob.mem{1} (_skp + 1152 + 1152) /\
       hpk{2} = load_array32 Glob.mem{1} (_skp + 1152 + 1152 + 32) /\
       pk{2}.`1 = load_array1152 Glob.mem{1} (_pkp) /\
       pk{2}.`2 = load_array32 Glob.mem{1} (_pkp + 1152) /\
       0 <= i{1} <= 4 /\ 
       forall k, 0<=k<i{1} =>
           loadW64 Glob.mem{1} (_skp + 2368 + k*8) =
                 pack8_t (W8u8.Pack.init (fun i => z{2}.[k*8+i])))
          (4 - i{1}).
  + move => &m z0; auto => /> &hr; rewrite /touches2 /load_array1152 /load_array32 !tP => 
       ?????? touch pk1vs pk2vs pk1v pk2v ??prev? ; rewrite !to_uintD_small /=.
    + by smt(). 
    do split; 1,9,12: by smt().
    + by move => a H1 H2; rewrite /storeW64 /loadW64 /stores /= !get_set_neqE_s /#.
    + by move => k kb; rewrite !initiE //= /storeW64 /loadW64 /stores /= !get_set_neqE_s /#.
    + move => k kb; rewrite !initiE //= /storeW64 /loadW64 
          /stores /= !get_set_neqE_s; 1..8: smt().     
      by rewrite pk1vs // initiE //=.
    + move => k kb; rewrite !initiE //= /storeW64 /loadW64 
         /stores /= !get_set_neqE_s; 1..8: smt().     
      by rewrite pk2vs // initiE //=.
    + by move => k kb; rewrite !initiE //= /storeW64 /loadW64 
         /stores /= !get_set_neqE_s;smt().
    + move => k kb; rewrite !initiE //= /storeW64 /loadW64 
         /stores /= !get_set_neqE_s; 1..8: smt(). 
    by rewrite pk1v // initiE //=.
    + move => k kb; rewrite !initiE //= /storeW64 /loadW64 
        /stores /= !get_set_neqE_s; 1..8: smt(). 
    by rewrite pk2v // initiE //=.
    + by smt().
    + move => k kbl kbh.
      case (k < i{hr}).
      + move => hk. 
        rewrite /storeW64 /loadW64 /stores /=; congr. 
        rewrite W8u8.Pack.packP => i ib; rewrite !initiE /=; 1,2: smt(). 
        rewrite !get_set_neqE_s; 1..8: smt(). 
        move : (prev k _); 1: by smt().
        rewrite !initiE 1:/# /storeW64 /loadW64 /stores /=.
        rewrite (inj_eq W8u8.pack8_t pack_inj) packP => H.
        move : (H i _); 1: smt().
        by rewrite !initiE //= initiE;  smt().
     move => hk.
     rewrite /storeW64 /loadW64 /stores /=.  
     congr;rewrite W8u8.Pack.packP => ii iib; rewrite !initiE /=; 1..2: smt(). 
     rewrite initiE /=; 1: smt(). 
     rewrite WArray32.WArray32.get64E !pack8bE 1..8:/# !initiE 1..8:/# /= /init8.  
      rewrite !WArray32.WArray32.initiE 1..8:/#.
     by smt(get_set_neqE_s get_set_eqE_s).

  auto => />;move => ????????touch????; do split. 
  + rewrite tP => k kb; rewrite !initiE 1..3:/# /=. 
  +  smt().
  +  smt().
  move => memL iL skpL.  
  split; 1: smt().
  move => ???touch2????????store???. 
  rewrite /load_array32 tP => k kb.
  rewrite !initiE //=.
  move : (store (k %/ 8) _); 1: smt().
  rewrite /storeW64 /loadW64 /stores /load_array32 /=. 
  rewrite (inj_eq W8u8.pack8_t pack_inj) packP => H.
  move : (H (k %%8) _); 1: smt().
  rewrite !initiE //=; 1,2:smt().
  by rewrite !initiE //=; smt(). 

swap {2} 2 2. 
swap {1} [2..3] 1; sp 4 1.

wp;conseq (_: _ ==>
to_uint skp{1} = _skp + 2368 /\ 
  touches2 Glob.mem{1} mem (_pkp) 1184 (_skp) 2432 /\
  sk{2} = load_array1152 Glob.mem{1} (_skp) /\
  pk{2}.`1 = load_array1152 Glob.mem{1} (_skp + 1152) /\
  pk{2}.`2 = load_array32 Glob.mem{1} (_skp + 2304) /\
  H_pk pk{2} = load_array32 Glob.mem{1} (_skp + 2336) /\
  pk{2}.`1 = load_array1152 Glob.mem{1} ( _pkp) /\ 
  pk{2}.`2 = load_array32 Glob.mem{1} (_pkp + 1152)); 1: by auto.

seq 1 1 : (#{/~Glob.mem{1}=mem}pre /\
  touches2 Glob.mem{1} mem _pkp 1184 _skp 2432 /\
  sk{2} = load_array1152 Glob.mem{1} _skp /\
  pk{2}.`1 = load_array1152 Glob.mem{1} _pkp /\ 
  pk{2}.`2 = load_array32 Glob.mem{1} (_pkp + 1152)).
 
call (mlkem_correct_kg_avx2 mem _pkp _skp).
auto => /> &1; rewrite /load_array1152 /load_array32 !tP /touches2 => ????????.
do split; 1,2,3: smt().
+ move =>  touch ????? [[resr11 resr12] resr2] memL touch2 /= [#]; rewrite !tP => r2 r11 r12. 
  do split.
  + by smt().
  + by move => k kb;  move : (r2 k _) => //; rewrite !initiE //.
  + by move => k kb;  move : (r11 k _) => //; rewrite !initiE //.
  by move => k kb;  move : (r12 k _) => //; rewrite !initiE //.

swap {1} 3 2. swap {1} 12 -4.

seq 8 0 : (#{/~to_uint skp{1} = _skp}pre /\
   to_uint skp{1} = _skp + 3*384 + 3*384 + 32 /\
   pk{2}.`1 = load_array1152 Glob.mem{1} (_skp + 1152) /\
  pk{2}.`2 = load_array32 Glob.mem{1} (_skp+ 2304)
).

+ wp;while {1} (#{/~to_uint skp{1} = _skp}{~s_skp{1} = skp{1}}pre /\ 
    aux{1} = (3 * 384 + 32) %/ 8 /\ 0<=i{1} <= aux{1} /\
    to_uint skp{1} = _skp + 3*384 + i{1}*8 /\
    (forall k, 0<= k < min (8 * i{1}) 1152  => 
         pk{2}.`1.[k] = Glob.mem{1}.[_skp + 3*384 + k]) /\
    (forall k, min (8 * i{1}) 1152 <= k < min (8 * i{1}) (1152 + 32) => 
         pk{2}.`2.[k-1152] = Glob.mem{1}.[_skp + 3*384 +  k])) 
    ((3 * 384 + 32) %/ 8 - i{1}).
  move => &m z;auto => /> &hr. rewrite /load_array32 /load_array1152 !tP /touches2.
  move => ???????touch pkv1 pkv2???prev1 prev2 ?;rewrite !to_uintD_small /=.
  + by rewrite of_uintK /= modz_small /=; smt().
  by smt().
  do split; 5..7:smt().
  + move => i ib ibb.
    rewrite /storeW64 /loadW64 /stores  /=.
    rewrite !get_set_neqE_s; 1..8:smt().
    by smt(get_set_neqE_s get_set_eqE_s).
  + move => i ib; rewrite !initiE //=.
    rewrite /storeW64 /loadW64 /stores  /=.
    rewrite !get_set_neqE_s; 1..8:smt().
    by smt(get_set_neqE_s get_set_eqE_s).
  + move => k kb; rewrite !initiE //=.
    rewrite /storeW64 /loadW64 /stores  /=.
    rewrite !get_set_neqE_s; 1..8:smt().
    by move : (pkv1 k kb); rewrite initiE //=.
  + move => k kb; rewrite !initiE //=.
    rewrite /storeW64 /loadW64 /stores  /=.
    rewrite !get_set_neqE_s; 1..8:smt().
    by move : (pkv2 k kb); rewrite initiE //=.
  + move => kk kkbl kkbh.
    rewrite /storeW64 /loadW64 /stores  /=.
    case (kk < i{hr} * 8).
    + by move => *; rewrite !get_set_neqE_s; smt().
    move => ?.
    rewrite !of_uintK /= modz_small;1:smt().
    move : (pkv1 kk _); 1: smt().
    rewrite initiE /=; 1: smt().
    by smt(get_set_neqE_s get_set_eqE_s).
  + move => kk kkbl kkbh.
    rewrite /storeW64 /loadW64 /stores  /=.
    case (kk < i{hr} * 8).
    + by move => *; rewrite !get_set_neqE_s; smt().
    move => ?.
    rewrite !of_uintK /= modz_small;1:smt().
    move : (pkv2 (kk - 1152) _); 1: smt().
    rewrite initiE /=; 1: smt().
    by smt(get_set_neqE_s get_set_eqE_s).
  + by smt().
  auto => /> &1 &2; rewrite /load_array1152 /load_array32 !tP.
  move =>  ??????????.
  rewrite to_uintD_small /=; 1: by smt().
  do split; 1..2: by smt(). 
  move => meml il skpl.
  rewrite !tP; split; 1: smt().
  move => ??????????; do split; 1: smt().
  + by move => *; rewrite initiE //= /#.
  by move => *; rewrite initiE //= /#.
   
seq 4 1 : 
(to_uint skp{1} = _skp + 2336 /\
   valid_disj_reg _pkp 1184 _skp 2432 /\
  touches2 Glob.mem{1} mem _pkp 1184 _skp 2432 /\
  sk{2} = load_array1152 Glob.mem{1} _skp /\
  pk{2}.`1 = load_array1152 Glob.mem{1} (_skp + 1152) /\
  pk{2}.`2 = load_array32 Glob.mem{1} (_skp + 2304) /\
  H_pk pk{2} = h_pk{1} /\ 
  pk{2}.`1 = load_array1152 Glob.mem{1} _pkp /\ pk{2}.`2 = load_array32 Glob.mem{1} (_pkp + 1152)).

ecall {1} (pkH_sha_avx2 (Glob.mem{1}) (_pkp) (h_pk{1})).
inline *; auto => /> &1 &2; rewrite /touches /touches2 /load_array1152 /load_array32 !tP => ??????????? pk1v pk2v .
+ move => i ib; congr; rewrite /H_pk; congr. 
  by smt(Array32.initiE Array1152.initiE Array32.tP Array1152.tP).

while {1} (#{/~to_uint skp{1} = _skp + 2336}pre /\ 0 <= i{1} <= 4 /\ to_uint skp{1} = _skp + 2336 + 8*i{1} /\ forall k, 0 <= k < i{1} * 8 => Glob.mem{1}.[_skp + 2336 + k] = ((H_pk pk{2})).[k]) (4 - i{1}).
move => &m z; auto => /> &1 &2; rewrite /load_array1152 /load_array32 /touches2 !tP.
move => ?????pkv1s pkv2s pkv1 pkv2 ??? prev ?. 
rewrite !to_uintD_small /= 1:/#.
do split.
+ move => i ib ih.
  rewrite /storeW64 /loadW64 /stores  /=. 
  by smt(get_set_neqE_s get_set_eqE_s).
+ move => i ib; rewrite !initiE //=.
  rewrite /storeW64 /loadW64 /stores  /=. 
  by smt(get_set_neqE_s get_set_eqE_s).
+ move => i ib; rewrite !initiE //=.
  rewrite /storeW64 /loadW64 /stores  /=.
  rewrite !get_set_neqE_s;1..8:smt().
  by move : (pkv1s i ib); rewrite initiE //=.
+ move => i ib; rewrite !initiE //=.
  rewrite /storeW64 /loadW64 /stores  /=.
  rewrite !get_set_neqE_s;1..8:smt().
  by move : (pkv2s i ib); rewrite initiE //=.
+ move => i ib; rewrite !initiE //=.
  rewrite /storeW64 /loadW64 /stores  /=.
  rewrite !get_set_neqE_s;1..8:smt().
  by move : (pkv1 i ib); rewrite initiE //=.
+ move => i ib; rewrite !initiE //=.
  rewrite /storeW64 /loadW64 /stores  /=.
  rewrite !get_set_neqE_s;1..8:smt().
  by move : (pkv2 i ib); rewrite initiE //=.
+ by smt().
+ by smt().
+ by smt().
+ move => k kbl kbh.
  case (k < (i{1} * 8)).
  + by move => kl;rewrite /storeW64 /loadW64 /stores  /=  !get_set_neqE_s;smt().
  move => kh. rewrite /storeW64 /loadW64 /stores  /=. 
  have -> :  (H_pk pk{m}).[k] = 
              (WArray32.WArray32.get64 ((WArray32.WArray32.init8 ("_.[_]" (H_pk pk{m}))))%WArray32.WArray32 i{1})%WArray32.WArray32 \bits8 (k %% 8); last  by smt(get_set_neqE_s get_set_eqE_s).
  rewrite /WArray32.WArray32.get64_direct.
  by rewrite pack8bE 1:/# initiE /= 1:/# /WArray32.WArray32.init8 WArray32.WArray32.initiE /#.

by smt().

auto => /> &1 &2.
rewrite /load_array1152 /load_array32 /touches2 !tP.
move => ???????pkv1s pkv2s pkv1 pkv2. 
do split.
+ move => i ib ih.
  rewrite /storeW64 /loadW64 /stores  /=. 
  by smt(get_set_neqE_s get_set_eqE_s).
move => memL iL skL; do split; 1: by smt().
move => *; split; 1: by smt().
by rewrite tP => i ib; smt(Array32.initiE).
qed.


lemma mlkem_kem_correct_enc mem _ctp _pkp _kp : 
   equiv [Jkem_avx2.M(Jkem_avx2.Syscall).__crypto_kem_enc_jazz ~ MLKEM.enc_derand: 
     valid_ptr _pkp (384*3 + 32) /\
     valid_disj_reg _ctp (3*320+128) _kp (32) /\
     Glob.mem{1} = mem /\ 
     to_uint ctp{1} = _ctp /\ 
     to_uint pkp{1} = _pkp /\
     randomnessp{1} = coins{2} /\
     to_uint shkp{1} = _kp /\
     pk{2}.`1 = load_array1152 mem _pkp /\
     pk{2}.`2 = load_array32 mem (_pkp + 3*384)
       ==> 
     touches2 Glob.mem{1} mem _ctp (3*320+128) _kp (32) /\
     let (c,k) = res{2} in
     c.`1 = load_array960 Glob.mem{1} _ctp /\
     c.`2 = load_array128 Glob.mem{1} (_ctp + 960) /\
     k = load_array32 Glob.mem{1} _kp
].
proc => /=.
seq 14 4 : (#[/1:-2]post 
      /\ valid_disj_reg _ctp 1088 _kp 32 
      /\ to_uint s_shkp{1} = _kp 
      /\ (forall k, 0<=k<32 => kr{1}.[k]=_K{2}.[k])); last first.
+ while {1} (#[/1:-2]post
      /\ aux{1} = 4 
      /\ 0<=i{1}<=4 
      /\ valid_disj_reg _ctp 1088 _kp 32 
      /\ to_uint shkp{1} = _kp 
      /\ (forall k, 0<=k<8*i{1} =>  _K{2}.[k] = (load_array32 Glob.mem{1} _kp).[k]) 
      /\ (forall k, 0<=k<32 => kr{1}.[k]=_K{2}.[k])) (aux{1} - i{1}).
  + auto => /> &hr H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11;do split;4:smt().
    + move : H;rewrite /touches2 => H a ab1 ab2. 
      rewrite storeW64E get_storesE /=. 
      by rewrite !to_uintD_small /= of_uintK /= modz_small /#.
    + move : H0; rewrite /load_array960 !tP => H0 k kb.
      rewrite initiE 1:/# /=.
      rewrite storeW64E get_storesE /=. 
      rewrite !to_uintD_small /= of_uintK /= modz_small 1..3:/# /=.
      by have := H0 k kb; rewrite initiE 1:/# /= /#.
    + move : H1; rewrite /load_array128 !tP => H1 k kb.
      rewrite initiE 1:/# /=.
      rewrite storeW64E get_storesE /=. 
      rewrite !to_uintD_small /= of_uintK /= modz_small 1..3:/# /=.
      by have := H1 k kb; rewrite initiE 1:/# /= /#. 
    + by smt().
    + move => k kbl kbh.
      move : H9; rewrite /load_array32 => H9.
      rewrite initiE 1:/# /=.
      rewrite storeW64E get_storesE /=. 
      rewrite !to_uintD_small /= of_uintK /= modz_small 1..3:/# /=.
      case (k < 8 * i{hr}).
      + move => kbb;have := H9 k _; 1: by smt().
        by rewrite initiE 1:/# /= /#. 
      rewrite !WArray64.WArray64.get64E. search pack8_t (\bits8).
      by rewrite !pack8bE // !initiE //= /init8 !WArray64.WArray64.initiE /#.
    by smt().
  auto => /> &1 &2 ?????????;split;  1: by smt().
  move => mm ii;do split => ???????; 1: smt().
  by rewrite /load_array32 tP => kk kkb; smt(Array32.initiE).

wp;call (mlkem_correct_enc_0_avx2 mem _ctp _pkp).
wp;ecall {1} (sha_g_avx2 buf{1} kr{1}).
wp;ecall {1} (pkH_sha_avx2 mem (_pkp) ((Array32.init (fun (i : int) => buf{1}.[32 + i])))).
seq 8 0 : (#pre /\ s_pkp{1} = pkp{1} /\ s_ctp{1} = ctp{1} /\  s_shkp{1} = shkp{1} /\ randomnessp{1} = Array32.init (fun i => buf{1}.[i])).
+ sp ; conseq />.
  while {1} (0<=i{1}<=aux{1} /\ aux{1} = 4 /\ randomnessp{1} = coins{2} /\  (forall k, 0<=k<i{1}*8 => randomnessp{1}.[k] = buf{1}.[k])) (aux{1} - i{1}); last first.
  + auto => /> &1 &2 *; split; 1: by smt().  
    move => buf i1; split; 1: smt(). 
    by move => *; rewrite tP => k kn; rewrite initiE //= /#. 
  move => &2 ?.
  auto => /> &1 il ih premv ihh; do split; 1,2,4:smt().
  move => k kl kh; rewrite initiE 1:/# /=.
  rewrite WArray64.WArray64.get8_set64_directE 1..2:/#.
  case (8 * i{1} <= k && k < 8 * i{1} + 8).
  + move => *. 
     rewrite WArray32.WArray32.get64E pack8bE 1:/# !initiE 1:/# /= /init8.  
     by rewrite !WArray32.WArray32.initiE /#.
  by move => *; rewrite /get8; rewrite WArray64.WArray64.initiE /#.
   
auto  => />  &1 &2; rewrite /load_array1152 /load_array32 /load_array128 /load_array960 /touches2 /touches !tP.
move => [#] ??????? pkv1 pkv2; do split.
+ by move => i ib; rewrite !initiE /= /#.
+ move => i ib; rewrite initiE /= 1:/# initiE /= 1:/# ifF 1:/#.
  rewrite /G_mhpk; congr;congr;congr;rewrite tP => k kb.
  + by rewrite !initiE 1,2,3:/# /= /H_msg ifF /#.
  rewrite initiE 1:/# /= /H_pk. 
  rewrite initiE 1:/# /= ifT 1:/#. 
  congr;congr.
  have -> : pk{2} = (pk{2}.`1,pk{2}.`2) by smt().
  apply pw_eq; rewrite tP => kk kkb.
  + by rewrite pkv1 /#.
  by rewrite pkv2 /#. 

move => ?? [cR1 cR2] /= memR touch [-> ->]; do split.
+ by move => a ? _; have := touch (a - to_uint ctp{1}); smt().

rewrite /KDF /G_mhpk /H_msg /H_pk => k kb kbh. 
rewrite !initiE //= 1:/# ifT 1:/#.
congr. congr. congr. 
+  rewrite tP => kk kkb.
   by rewrite !initiE /= 1,2,3: /# ifF /#. 
have -> : pk{2} = (pk{2}.`1,pk{2}.`2) by smt().
rewrite tP => kk kkb. 
pose xx := (SHA3_256_1184_32 (pk{2}.`1, pk{2}.`2)).[kk].
rewrite !initiE 1:/# /= initiE 1:/# /= ifT 1:/#.
rewrite /xx;congr;congr.
apply pw_eq; rewrite tP => kkk kkkb.
+ by rewrite pkv1 /#.
by rewrite pkv2 /#. 
qed.

require import StdOrder. 
import IntOrder.

lemma verify_correct_h mem (_ctp : int) ctp1 :
  hoare [Jkem_avx2.M(Jkem_avx2.Syscall).__verify : 
             Glob.mem = mem /\ valid_ptr _ctp 1088 /\
             to_uint ctp = _ctp /\ ctpc = ctp1 ==>
             Glob.mem = mem /\
             (Array1088.init (fun i => loadW8 mem (_ctp + i)) = ctp1 => 
                       res = W64.of_int 0) /\
             (Array1088.init (fun i => loadW8 mem (_ctp + i)) <> ctp1 => 
                       res = W64.of_int 1)].
proc => /=.
seq 8 : (#post); last first.
wp. conseq />. while(i=1088 /\ aux=1088 /\ #pre); 1: by auto => />. 
+ (*conseq />; 1: by smt(). *)
  conseq />; first by move => /> *; split; smt().
  auto => />.  
  move => &hr H H1 _cnd H2 H3.
  split. 
  + by move => H4; move : (H2 H4) => -> /=; rewrite W64.WRingA.oppr0 to_uint_eq W64.shr_div_le //.
  + move => H5; move : (H3 H5) => -> /=; rewrite W64.minus_one /= wordP => i ib.
    by rewrite /(`>>`) shrwE ib /= /(W64.one) /= /bits2w /= initiE //= /int2bs /= /mkseq /= -iotaredE /= /#. 

wp; while (#pre /\ 0 <= i{hr} <= 34 /\ aux{hr} = 34 /\ 0<=to_uint cnd<256 /\
           (to_uint h{hr} = 0 <=> 
            forall k, 0 <= k < i{hr}*32 => loadW8 mem (_ctp + k) = ctp1.[k])); last first.
+ auto => /> &hr ??; split; 1: by smt().
  move => h i ??? [HL HR]; split; last first.
  + rewrite tP => H1.
    rewrite /VPTEST_256 /= /ZF_of /= ifT //.
    move : H1; rewrite negb_forall /= => [[k H]]. 
    move : H; rewrite negb_imply  /= => [# H1 H2 H3].
    rewrite initiE //= in H3.
    rewrite implybE in HL; elim HL; smt(to_uint0). 

  + rewrite tP => H1.
    rewrite /VPTEST_256 /= /ZF_of /= ifF //.
    rewrite implybE in HR; elim HR.
    +  rewrite negb_forall /= => [[k H]].  
       move : H; rewrite negb_imply  /= => [# H2 H3 H4].
       smt(Array1088.initiE).
    smt(W256.to_uint_eq W256.to_uint0).

auto => /> &hr ?????? [HL HR] ?.
pose x := 
      ((WArray1088.WArray1088.get256 ((WArray1088.WArray1088.init8 ("_.[_]" ctp1)))%WArray1088.WArray1088 i{hr})) `^`
        loadW256 mem (to_uint (ctp{hr} + (of_int (32 * i{hr}))%W64)).
do split; 1..2: by smt().
+ move => H0 k kbl kbh.

  have H1 : to_uint h{hr} = 0. 
  + have : h{hr} = W256.zero; last by rewrite to_uint_eq /=.
    have : (h{hr} `|` x) = W256.zero by rewrite to_uint_eq  H0 /=.
    by rewrite !wordP; smt(orwE zerowE).

  have H2 : x = W256.zero.
  + have : (h{hr} `|` x) = W256.zero by rewrite to_uint_eq  H0 /=. 
    by rewrite !wordP; smt(orwE zerowE).

  case (k < i{hr}*32); 1: by move => *; apply (HL _ _) => // /#. 
 
  move => kv.
  move : H2; rewrite /x W256.WRing.addr_eq0 /oppw /=. 
  rewrite /init8 /loadW256 /loadW8 /get256_direct wordP => H2.
  apply W8.wordP => j jb.
  move : (H2 ((k - i{hr} * 32) * 8 + j) _). smt().
  rewrite !pack32wE /=; 1,2: smt().
  rewrite !initiE /=; 1,2: smt().
  rewrite to_uintD_small /=; 1: by rewrite /= of_uintK /=; by smt(W64.to_uint_cmp).  
  rewrite /= of_uintK /= (modz_small _  18446744073709551616) 1:/#.
  rewrite WArray1088.WArray1088.initiE 1:/# /=. smt().

move => H0.
have -> : h{hr} = W256.zero by rewrite to_uint_eq /= /#.
rewrite or0w;have -> : x = W256.zero; last by auto.
rewrite wordP => k kb; rewrite zerowE /x.
move : H0;rewrite /init8 /loadW256 /loadW8 /get256_direct => H0. 
pose xx := pack32_t _.
pose yy := pack32_t _.
have -> : xx = yy; last by rewrite xorwK_s //.
rewrite /xx /yy wordP => j jb.
  rewrite !pack32wE /=; 1,2: smt().
  rewrite !initiE /=; 1,2: smt().
  rewrite to_uintD_small /=; 1: by rewrite /= of_uintK /=; by smt(W64.to_uint_cmp).  
  rewrite /= of_uintK /= (modz_small _  18446744073709551616) 1:/#.
  rewrite WArray1088.WArray1088.initiE 1:/# /=. smt().
qed.

lemma verify_ll : islossless Jkem_avx2.M(Jkem_avx2.Syscall).__verify.
proc.
seq 8 : (#post) => //; last first.
wp. conseq />. while(i=1088 /\ aux=1088 /\ #pre) (1088 - aux); 1,2:   by auto => />. 
wp.
while (0 <= i{hr} <= 34 /\ aux{hr} = 34) (34 - i{hr}).
auto => /> /#.
auto => /> /#. 
qed.

lemma verify_correct mem (_ctp : int) ctp1 :
  phoare [Jkem_avx2.M(Jkem_avx2.Syscall).__verify : 
             Glob.mem = mem /\ valid_ptr _ctp 1088 /\
             to_uint ctp = _ctp /\ ctpc = ctp1 ==>
             Glob.mem = mem /\
             (Array1088.init (fun i => loadW8 mem (_ctp + i)) = ctp1 => 
                       res = W64.of_int 0) /\
             (Array1088.init (fun i => loadW8 mem (_ctp + i)) <> ctp1 => 
                       res = W64.of_int 1)] = 1%r 
   by conseq verify_ll (verify_correct_h mem _ctp ctp1).

lemma cmov_correct_h _dst _src _cnd mem:
   hoare [Jkem_avx2.M(Jkem_avx2.Syscall).__cmov : 
             Glob.mem = mem /\ valid_ptr _dst 32 /\
             src = _src /\ cnd = _cnd /\ to_uint dst = _dst ==>
             touches mem Glob.mem _dst 32 /\
             (_cnd = W64.of_int 0 => 
               (Array32.init (fun i => loadW8 Glob.mem (_dst + i))) = _src) /\
             (_cnd = W64.of_int 1 => 
               (Array32.init (fun i => loadW8 Glob.mem (_dst + i))) = 
                (Array32.init (fun i => loadW8 mem (_dst + i))))].
proc => /=.
seq 1 : (#{/~cnd}pre /\ (_cnd = W64.zero => cnd = W64.zero) /\
                (_cnd = W64.one => cnd = W64.onew));
  1: by auto => /> &1 ?? /=; split; [ by ring | by rewrite W64.minus_one /=].
seq 5 : (#post); last first.
+ by wp; conseq />; while(i=32 /\ #pre); auto => /> /#. 

unroll 5.

seq 5 : (#post /\ aux{hr}= 1 /\ i{hr}=1); last first.
+ wp; conseq />; while(i=1 /\ aux=1 /\ #pre); auto => /> /#. 

rcondt 5; 1: by move => *; auto => />.

auto => /> &hr H H0 H1 H2.

have msb1 : forall i,  0 <= i < 8 => msb (W64.onew \bits8 i) = true.
+ move => i ib; rewrite /msb /=.
  have -> : W64.onew \bits8 i = W8.onew.
  + rewrite wordP => k kb.
    rewrite onewE /= kb /= bits8iE //= /#.
  by rewrite  to_uint_onew /=.

have msb0 : forall i, 0 <= i <8 => msb (W64.zero \bits8 i) = false.
+ move => i ib; rewrite /msb /=.
  have -> : W64.zero \bits8 i = W8.zero.
  + rewrite wordP => k kb.
    rewrite zerowE  /= bits8iE //= /#.
  by rewrite to_uint0 /=.

do split.
+ rewrite /touches => a ab.
  rewrite /storeW256 /loadW256 /loads /stores /=.
  by do 32!(rewrite get_setE ifF 1:/#);smt().

+ move =>czero; move : (H1 czero) => -> /=;rewrite tP => k kb.
rewrite initiE //= /storeW256 /=.
have HH : forall ii, 0<=ii <32 => VPBLENDVB_256 ((WArray32.WArray32.get256_direct ((WArray32.WArray32.init8 ("_.[_]" _src))) 0))
          (loadW256 mem (to_uint dst{hr})) (VPBROADCAST_4u64 W64.zero) \bits8
        ii = _src.[ii]; last first. 
+ rewrite !HH //=.
  by rewrite /loadW8 /stores /= !get_setE /= /#.
move => ii iib.
rewrite /get256_direct /init8 /loadW256 /loadW8 /= wordP => i ib.
rewrite /VPBLENDVB_256 /VPBROADCAST_4u64 /(\bits8) -iotaredE /= /VPBLENDVB_128 /= !msb0 //=  initiE //=.
rewrite pack32E initiE /= 1:/# /of_list initiE /= /#.
 
+ move =>cone; move : (H2 cone) => -> /=;rewrite tP => k kb.
rewrite initiE //= /storeW256 /=.
have HH : forall ii, 0<=ii <32 => VPBLENDVB_256 ((WArray32.WArray32.get256_direct ((WArray32.WArray32.init8 ("_.[_]" _src))) 0))
        (loadW256 mem (to_uint dst{hr})) (VPBROADCAST_4u64 W64.onew) \bits8
              ii = ((init (fun (i0 : int) => loadW8 mem (to_uint dst{hr} + i0))))%Array32.[ii]; last first. 
+ rewrite !HH //=.
  by rewrite initiE //= /loadW8 /stores /= !get_setE /= /#.
move => ii iib.
rewrite /get256_direct /init8 /loadW256 /loadW8 /= wordP => i ib.
rewrite /VPBLENDVB_256 /VPBROADCAST_4u64 /(\bits8) -iotaredE /= /VPBLENDVB_128 /= !msb1 //=  initiE //=.
by rewrite pack32E initiE /= 1:/# /of_list !initiE /= /#.
qed.

lemma cmov_ll : islossless Jkem_avx2.M(Jkem_avx2.Syscall).__cmov.
proc => /=.
seq 6 : (#post) => //; last first.
+ by wp; conseq />; while(i=32 /\ #pre) (32-i); auto => /> /#. 

unroll 6.

+ wp; conseq />; while(i=1 /\ aux=1 /\ #pre) (1-i); auto => /> /#. 

qed.


lemma cmov_correct _dst _src _cnd mem:
   phoare [Jkem_avx2.M(Jkem_avx2.Syscall).__cmov : 
             Glob.mem = mem /\ valid_ptr _dst 32 /\
             src = _src /\ cnd = _cnd /\ to_uint dst = _dst ==>
             touches mem Glob.mem _dst 32 /\
             (_cnd = W64.of_int 0 => 
               (Array32.init (fun i => loadW8 Glob.mem (_dst + i))) = _src) /\
             (_cnd = W64.of_int 1 => 
               (Array32.init (fun i => loadW8 Glob.mem (_dst + i))) = 
                (Array32.init (fun i => loadW8 mem (_dst + i))))] = 1%r
    by conseq cmov_ll (cmov_correct_h _dst _src _cnd mem).

lemma mlkem_kem_correct_dec mem _ctp _skp _shkp : 
   equiv [Jkem_avx2.M(Jkem_avx2.Syscall).__crypto_kem_dec_jazz ~ MLKEM.dec: 
     valid_ptr _ctp (3*320+128) /\
     valid_ptr _skp (384*3 + 384*3 + 32 + 32 + 32+ 32) /\
     valid_ptr _shkp 32 /\
     Glob.mem{1} = mem /\ 
     to_uint shkp{1} = _shkp /\
     to_uint ctp{1} = _ctp /\
     to_uint skp{1} = _skp /\
     sk{2}.`1 = load_array1152 Glob.mem{1} _skp /\
     sk{2}.`2.`1 = load_array1152 Glob.mem{1} (_skp + 1152) /\
     sk{2}.`2.`2 = load_array32 Glob.mem{1} (_skp + 1152 + 1152) /\
     sk{2}.`3 = load_array32 Glob.mem{1} (_skp + 1152 + 1152 + 32) /\
     sk{2}.`4 = load_array32 Glob.mem{1} (_skp + 1152 + 1152 + 32 + 32) /\
     let (c1,c2) = cph{2} in
       c1 = load_array960 Glob.mem{1} _ctp /\
       c2 = load_array128 Glob.mem{1} (_ctp + 960)
       ==> 
     touches Glob.mem{1} mem _shkp 32 /\
     res{2} = load_array32 Glob.mem{1} _shkp
].
proc => /=. sp 0 1. swap {1} [4..5] 12.

seq 4 1 : (#pre /\ aux{1} = m{2}); 
  1: by call (mlkem_correct_dec mem _ctp _skp); 1: by auto => /> /#.

swap {1} 7 1.
seq 7 1 : (#pre /\ 
           (forall k, 0<=k<32 => buf{1}.[k] = m{2}.[k]) /\
           (forall k, 0<=k<32 => kr{1}.[k] = _K{2}.[k]) /\
           (forall k, 0<=k<32 => kr{1}.[k+32] = r{2}.[k])).
ecall {1} (sha_g_avx2 buf{1} kr{1}).
wp; conseq (_: _ ==> 
   (forall k, 0<=k<32 => buf{1}.[k] = m{2}.[k]) /\
   (forall k, 32<=k<64 => buf{1}.[k] = mem.[_skp + 2336 + k - 32]) /\
   (forall k, 0<=k<32 => buf{1}.[k] = aux{1}.[k])).
+ auto => /> &1 &2; rewrite /load_array32 !tP => ?????????buf bvl bvh ; split.
  + move => k kbl kbh; rewrite initiE 1:/# /= kbh /= /G_mhpk; congr; congr;congr.
    rewrite tP => i ib; rewrite initiE //= /#.
    by rewrite tP => i ib; rewrite !initiE  /#. 
  + move => k kbl kbh; rewrite initiE 1:/# /= ifF 1:/# /= /G_mhpk; congr; congr;congr.
    rewrite tP => i ib; rewrite initiE //= /#.
    by rewrite tP => i ib; rewrite !initiE  /#. 
  
while {1} (0<=i{1}<=4 /\ aux_0{1} = 4  /\ to_uint hp{1} = _skp + 2336 /\ Glob.mem{1} = mem /\
             valid_ptr _skp (384*3 + 384*3 + 32 + 32 + 32+ 32) /\
             (forall (k : int), 32 <= k && k < 32 + 8*i{1} => buf{1}.[k] = mem.[_skp + 2336 + k - 32]) /\
             forall (k : int), 0 <= k && k < 32 => buf{1}.[k] = aux{1}.[k]) (4 - i{1}); last first. 
  + auto => /> &1 &2; rewrite /valid_ptr => ???????? /=.
    have -> /= : cph{2} = (cph{2}.`1,cph{2}.`2) by smt().
    rewrite /load_array960 /load_array128 !tP => [#] cph1v cph2v.
    do split.
    + by rewrite /(`|>>`) /(`<<`) /= to_uintD_small of_uintK /= /#. 
    + by smt().
    + by move => k kbl kbh; rewrite initiE /= /#.
    by smt().
  move => *; auto => /> &hr ????????; do split; 1..2,5: by smt().
  + move => k kbl kbh; rewrite initiE //= 1:/#.
    rewrite /storeW64 /loadW64 /stores  /=. 
    rewrite WArray64.WArray64.get8_set64_directE 1..2:/#.
    case (32 + 8 * i{hr} <= k && k < 32 + 8 * i{hr} + 8).
    + by move => *; rewrite pack8bE 1:/# initiE /= 1:/# to_uintD_small /= of_uintK /= modz_small /#. 
    by move => *; rewrite /WArray64.WArray64.get8 WArray64.WArray64.initiE /= /#.  
  move => k kbl kbh; rewrite initiE /= 1:/# WArray64.WArray64.get8_set64_directE 1..2:/#. 
  case (32 + 8 * i{hr} <= k && k < 32 + 8 * i{hr} + 8).
  + by move => *; rewrite pack8bE 1:/# initiE /= 1:/# to_uintD_small /= of_uintK /= modz_small /#. 
  by move => *; rewrite /WArray64.WArray64.get8 WArray64.WArray64.initiE /= /#.  
  
swap {2} 1 1.  
seq 4 1 : (#pre /\ to_uint s_skp{1} = _skp /\ 
           ctpc{1} = Array1088.init (fun i => if i < 960 then c{2}.`1.[i] else c{2}.`2.[i-960])).
+ wp;call (mlkem_correct_enc_1_avx2 mem (_skp + 1152)).

  auto => /> &1 &2 ???????; rewrite /load_array1152 /load_array32 /load_array960 !tP => ?????; do split; 1..2: by smt().
  + by move => i ib; rewrite initiE /= /#.
  + by rewrite /(`|>>`) /(`<<`) /= to_uintD_small of_uintK /= /#. 
  + by move => i ib; rewrite initiE /= /#.
  move => /= ? ? bufv ? krv rl rr H. 
  rewrite (_: rr = (rr.`1,rr.`2)) 1:/# /= in H.
  rewrite tP => i ib.
  rewrite !initiE //=. by  smt(Array128.initiE Array960.initiE).

sp 3 0; seq 1 0 : (#pre /\ 
                  (c{2}  = cph{2} => cnd{1} = W64.of_int 0) /\
                  (c{2}  <> cph{2} => cnd{1} = W64.of_int 1)).
+  conseq (_: _ ==> (c{2}  = cph{2} => cnd{1} = W64.of_int 0) /\
                  (c{2}  <> cph{2} => cnd{1} = W64.of_int 1)); 1: smt(). 
   ecall {1} (verify_correct mem _ctp ctpc{1}).
   auto => /> &1 &2; rewrite /load_array960 /load_array128 !tP.
   move  => ????????cphv????rst Heq Hdiff.
   rewrite (_: cph{2} = (cph{2}.`1, cph{2}.`2)) /= in cphv; 1: by smt().
   move : cphv;rewrite !tP ; move => [cphv1 cphv2].
   split.
   + move => ceq; rewrite (Heq _); last by done.
     move => i0 ib; rewrite !initiE //=. 
     case (i0 < 960).
     + by move => ibb; rewrite ceq cphv1 1: /# initiE /= /#.
     by move => ibb; rewrite ceq cphv2 1: /# initiE /= /#. 
   move => neq;rewrite Hdiff. 
   have : exists i0, 0<= i0 < 1088 /\ 
     (Array1088.init (fun (i1 : int) => loadW8 mem (to_uint s_ctp{1} + i1))).[i0] <>
     (Array1088.init (fun (i1 : int) => if i1 < 960 then c{2}.`1.[i1] else c{2}.`2.[i1 - 960])).[i0]; last by smt().
   case (c{2}.`1 <> cph{2}.`1).
   + move => neq1. rewrite tP in neq1.   
     have [k kb] : exists k, 0<=k<960 /\ c{2}.`1.[k] <> cph{2}.`1.[k] by smt().
     exists k; split; 1: by smt().
     rewrite !initiE /= 1,2:/#. 
     move : (cphv1 k _); 1: smt().
     by rewrite initiE /= /#.
   + move => eq1. 
     have neq2 : c{2}.`2 <> cph{2}.`2 by move : neq eq1; smt().
     rewrite tP in neq2.   
     have [k kb] : exists k, 0<=k<128 /\ c{2}.`2.[k] <> cph{2}.`2.[k] by smt().
     exists (k + 960); split; 1: by smt().
     rewrite !initiE /= 1,2:/#. 
     move : (cphv2 k _); 1: smt().
     by rewrite initiE /= /#.
  done.


ecall {1} (cmov_correct (to_uint shkp{1}) (Array32.init (fun (i_0 : int) => kr{1}.[0 + i_0])) cnd{1} Glob.mem{1}).

wp;ecall{1} (j_shake_avx2  Glob.mem{1} (to_uint shkp{1}) (to_uint zp{1}) (to_uint ctp{1})).

+ auto => /> &1 &2 ???????; rewrite /load_array1152 /load_array32 !tP => ?cphv????ceq cdif.
do split;1,2:
  by rewrite /(`|>>`) /(`<<`) /= to_uintD_small of_uintK /= /#. 
move => ??????mm0 tt0 hashv;do split.
+ move => badc mm back c0 c1;split.
  + by move : back tt0 => /#.
  + have -> : (init (fun (i0 : int) => mm.[to_uint shkp{1} + i0]))%Array32 =
              (init (fun (i0 : int) => mm0.[to_uint shkp{1} + i0]))%Array32.
    move : (c1 (cdif badc)).
    rewrite !tP => H k kb.
    by rewrite (H k kb) !initiE 1,2:/# /= /loadW8 /loads.
  rewrite hashv /J;congr.
  + rewrite tP => k kb; rewrite !initiE 1,2:/# /=.
    by rewrite /(`|>>`) /(`<<`) /= to_uintD_small of_uintK /= /#. 
  rewrite (_: cph{2} = (cph{2}.`1, cph{2}.`2)) 1: /# /=.
  rewrite (_: cph{2} = (cph{2}.`1, cph{2}.`2)) 1: /# /= in cphv.
  by move : cphv => [-> ->]; rewrite /load_array960 /load_array128 /#.

move => goodc mm back c0 c1;split.
  + by move : back tt0 => /#.
  + move : (c0 (ceq goodc)).
    rewrite !tP => H k kb.
    by rewrite (H k kb) initiE /#.
qed.

