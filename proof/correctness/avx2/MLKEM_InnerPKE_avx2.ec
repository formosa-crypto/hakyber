require import AllCore IntDiv List.
from Jasmin require import JModel.
require import Array16 Array25 Array32 Array33 Array128 Array136 Array256 Array768 Array960 Array1088 Array2304.
require import List_extra.
require import MLKEM_Poly  MLKEM_PolyVec MLKEM_InnerPKE.
require import MLKEM_Poly_avx2_proof.
require import MLKEM_Poly_avx2_vec.
require import MLKEM_Poly_avx2_prevec.
require import MLKEM_PolyVec_avx2_proof.
require import MLKEM_PolyVec_avx2_vec.
require import MLKEMFCLib.
require import Jkem_avx2 Jkem.
require import NTT_avx2 NTT_AVX_j.
require import NTT_Fq NTT_AVX_Fq.
require import MLKEM_avx2_equivs.
require import Montgomery16.
require import AVX2_Ops.


import GFq Rq Sampling Serialization Symmetric VecMat InnerPKE MLKEM Fq Correctness.

import MLKEM_Poly.
import MLKEM_PolyVec.
import MLKEM_PolyvecAVX.
import MLKEM_PolyAVXVec.
import NTT_Avx2.
import WArray136 WArray32 WArray128.
import WArray512 WArray256.

(* move somewhere else *)

lemma prod (x:'a*'b) :
 x = (x.`1,x.`2). smt(). qed.

lemma bits8_W32u8 ws i :
  W32u8.pack32_t ws \bits8 i = if 0 <= i < 32 then ws.[i] else W8.zero.
apply W8.wordP => j hj.
case (0 <= i < 32) => hi. rewrite  W32u8.pack32bE //. rewrite get_out //. qed.

lemma ianda a b c : a => (b => c) => ((a => b) => c). smt(). qed.

lemma if_eq (a:bool) (b c d:'a) : (a => (b=d)) => (!a => (c=d)) => (if a then b else c) = d.
move => T F. case a => />. qed.

(* shake assumptions *)

op SHAKE256_ABSORB4x_33 : W8.t Array33.t -> W8.t Array33.t -> W8.t Array33.t -> W8.t Array33.t -> W256.t Array25.t.
op SHAKE256_SQUEEZENBLOCKS4x : W256.t Array25.t -> W256.t Array25.t * W8.t Array136.t * W8.t Array136.t * W8.t Array136.t * W8.t Array136.t.

axiom shake_absorb4x state seed1 seed2 seed3 seed4 : 
   phoare [ Jkem_avx2.M(Jkem_avx2.Syscall)._shake256_absorb4x_33 : 
               arg = (state,seed1,seed2,seed3,seed4) ==>
               res = SHAKE256_ABSORB4x_33 seed1 seed2 seed3 seed4 ] = 1%r.

axiom shake_squeezenblocks4x state buf1 buf2 buf3 buf4 : 
   phoare [ Jkem_avx2.M(Jkem_avx2.Syscall).__shake256_squeezenblocks4x : 
               arg = (state,buf1,buf2,buf3,buf4) ==>
               res = SHAKE256_SQUEEZENBLOCKS4x state ] = 1%r.

axiom shake4x_equiv (sn1 sn2 sn3 sn4: W8.t Array33.t) (s1 s2 s3 s4 : W8.t Array32.t) n1 n2 n3 n4 :
  s1 = Array32.init (fun i => sn1.[i]) =>
  s2 = Array32.init (fun i => sn2.[i]) =>
  s3 = Array32.init (fun i => sn3.[i]) =>
  s4 = Array32.init (fun i => sn4.[i]) =>
  n1 = sn1.[32] => n2 = sn2.[32] => n3 = sn3.[32] => n4 = sn4.[32] =>
  Array128.init ("_.[_]" (SHAKE256_SQUEEZENBLOCKS4x (SHAKE256_ABSORB4x_33 sn1 sn2 sn3 sn4)).`2) = SHAKE256_33_128 s1 n1 /\
  Array128.init ("_.[_]" (SHAKE256_SQUEEZENBLOCKS4x (SHAKE256_ABSORB4x_33 sn1 sn2 sn3 sn4)).`3) = SHAKE256_33_128 s2 n2 /\
  Array128.init ("_.[_]" (SHAKE256_SQUEEZENBLOCKS4x (SHAKE256_ABSORB4x_33 sn1 sn2 sn3 sn4)).`4) = SHAKE256_33_128 s3 n3 /\
  Array128.init ("_.[_]" (SHAKE256_SQUEEZENBLOCKS4x (SHAKE256_ABSORB4x_33 sn1 sn2 sn3 sn4)).`5) = SHAKE256_33_128 s4 n4.

axiom sha3equiv : 
 equiv [ (* is this in the sha3 paper? *)
Jkem_avx2.M(Jkem_avx2.Syscall)._sha3_512_32 ~Jkem.M(Jkem.Syscall)._sha3512_32 : ={arg} ==> ={res}].

lemma keccakf1600_set_row_ll : islossless M(Syscall).keccakf1600_set_row.
proc. by unroll for ^while; auto. qed.

lemma keccakf1600_rho_offsets_ll : islossless M(Syscall).keccakf1600_rho_offsets.
proc. by unroll for ^while; islossless. qed.

lemma keccakf1600_rhotates_ll : islossless M(Syscall).keccakf1600_rhotates.
proc. by call keccakf1600_rho_offsets_ll; islossless. qed.

lemma keccakf1600_theta_rol_ll : islossless M(Syscall).keccakf1600_theta_rol.
proc. by unroll for ^while; islossless. qed.

lemma keccakf1600_theta_sum_ll : islossless M(Syscall).keccakf1600_theta_sum.
proc. by do 6!(unroll for ^while); islossless. qed.

lemma keccakf1600_rol_sum_ll : islossless M(Syscall).keccakf1600_rol_sum.
proc.
while (x <= 5) (5 - x); auto; last smt().
conseq => /=; call keccakf1600_rhotates_ll; auto => /#.
qed.

lemma keccakf1600_round_ll : islossless Jkem.M(Syscall).keccakf1600_round.
proc; auto.
while (y <= 5) (5 - y); auto.
+ call keccakf1600_set_row_ll.
  call keccakf1600_rol_sum_ll.
  auto; smt().
call keccakf1600_theta_rol_ll.
call keccakf1600_theta_sum_ll.
auto; smt().
qed.

lemma keccakf1600_ll : islossless Jkem.M(Syscall)._keccakf1600_.
proc; auto.
call (:true); auto.
call (:true); auto.
while (to_uint c <= 24 /\ to_uint c %% 2 = 0) (24 - to_uint c); auto; last by move => /> *; rewrite ultE to_uint_small //= /#.
call keccakf1600_round_ll; auto.
call keccakf1600_round_ll; auto.
move => /> ??; rewrite ultE to_uintD_small to_uint_small //= /#.
qed.

lemma sha3ll : islossless Jkem.M(Jkem.Syscall)._shake256_128_33.
proof.
proc.
unroll for 12; wp; conseq => /=.
call keccakf1600_ll; auto.
conseq => /=.
unroll for ^while; auto.
conseq => /=.
inline *; unroll for ^while; auto.
qed.

(*
axiom shake128_equiv_absorb : equiv [ M(Syscall)._shake128_absorb34 ~ 
   Jkem_avx2.M(Jkem_avx2.Syscall)._shake128_absorb34   :
      ={state, in_0} ==> ={res}].
axiom shake128_equiv_squeezeblock : equiv [  M(Syscall)._shake128_squeezeblock ~
     Jkem_avx2.M(Jkem_avx2.Syscall)._shake128_squeezeblock  :
      ={state, out} ==> ={res}].
*)

lemma rng_iotared i n :
  (0 <= i < n) = (i \in iotared 0 n).
rewrite iotaredE mem_iota //= andaE //. qed.

op pack16x8 (x:('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)) : 'a Array128.t = Array128.init (fun i =>
 if 0 <= i < 16 then x.`1.[i%%16]
 else if 16 <= i < 32 then x.`2.[i%%16]
 else if 32 <= i < 48 then x.`3.[i%%16]
 else if 48 <= i < 64 then x.`4.[i%%16]
 else if 64 <= i < 80 then x.`5.[i%%16]
 else if 80 <= i < 96 then x.`6.[i%%16]
 else if 96 <= i < 112 then x.`7.[i%%16]
 else x.`8.[i%%16]) axiomatized by pack16x8E.

op unpack16x8 (x:'a Array128.t) : ('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t) =
 (Array16.init (fun i => x.[i+16*0])
 ,Array16.init (fun i => x.[i+16*1])
 ,Array16.init (fun i => x.[i+16*2])
 ,Array16.init (fun i => x.[i+16*3])
 ,Array16.init (fun i => x.[i+16*4])
 ,Array16.init (fun i => x.[i+16*5])
 ,Array16.init (fun i => x.[i+16*6])
 ,Array16.init (fun i => x.[i+16*7])) axiomatized by unpack16x8E.

lemma unpack16x8K (w:'a Array128.t) :
  pack16x8 (unpack16x8 w) = w.
rewrite pack16x8E unpack16x8E tP => i Hi. rewrite !initiE //=. rewrite !initiE //= 1..8:/#.
smt(). qed.

lemma pack16x8K (w:('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)) :
  unpack16x8 (pack16x8 w) = w.
rewrite pack16x8E unpack16x8E => />. rewrite (_:w=(w.`1,w.`2,w.`3,w.`4,w.`5,w.`6,w.`7,w.`8)) => />. smt(). progress.
rewrite tP => i Hi. rewrite !initiE //= /#. 
rewrite tP => i Hi; rewrite !initiE //= !initiE //= /#.
rewrite tP => i Hi. rewrite !initiE //= !initiE //= /#. 
rewrite tP => i Hi. rewrite !initiE //= !initiE //= /#. 
rewrite tP => i Hi. rewrite !initiE //= !initiE //= /#. 
rewrite tP => i Hi. rewrite !initiE //= !initiE //= /#.
rewrite tP => i Hi. rewrite !initiE //= !initiE //= /#.
rewrite tP => i Hi. rewrite !initiE //= !initiE //= /#.
qed.

op pack128x2 (x:'a Array128.t * 'a Array128.t) : 'a Array256.t = Array256.init (fun i =>
  if 0 <= i < 128 then x.`1.[i%%128]
  else x.`2.[i%%128]) axiomatized by pack128x2E.

op unpack128x2 (x:'a Array256.t) : ('a Array128.t * 'a Array128.t) =
 (Array128.init (fun i => x.[i+128*0])
 ,Array128.init (fun i => x.[i+128*1])) axiomatized by unpack128x2E.

lemma unpack128x2K (w:'a Array256.t) :
  pack128x2 (unpack128x2 w) = w.
rewrite pack128x2E unpack128x2E tP => i Hi. rewrite !initiE //=. rewrite !initiE //= 1..2:/#.
smt(). qed.

lemma pack128x2K (w:('a Array128.t)*('a Array128.t)) :
  unpack128x2 (pack128x2 w) = w.
rewrite pack128x2E unpack128x2E => />. rewrite (_:w=(w.`1,w.`2)) => />. smt(). progress.
rewrite tP => i Hi. rewrite !initiE //= /#. 
rewrite tP => i Hi. rewrite !initiE //= !initiE //= /#. 
qed.

abbrev is16u16x8 (x:t16u16*t16u16*t16u16*t16u16*t16u16*t16u16*t16u16*t16u16) (y:vt16u16*vt16u16*vt16u16*vt16u16*vt16u16*vt16u16*vt16u16*vt16u16) = is16u16 x.`1 y.`1 /\ is16u16 x.`2 y.`2 /\ is16u16 x.`3 y.`3 /\ is16u16 x.`4 y.`4 /\ is16u16 x.`5 y.`5 /\ is16u16 x.`6 y.`6 /\ is16u16 x.`7 y.`7 /\ is16u16 x.`8 y.`8.

abbrev nttunpack128x16 ['a] (x:('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)*('a Array16.t)) = unpack16x8 (nttunpack128 (pack16x8 x)).

lemma rng_perm_nttunpack128 i :
  0 <= i < 128 => 
  0 <= nth witness perm_nttunpack128 i < 128.
move => *. rewrite perm_nttunpack128E => />. smt(). qed.

lemma nttunpack128x2 (w:'a Array256.t) :
  unpack128x2 (nttunpack w) = (nttunpack128 (unpack128x2 w).`1,nttunpack128 (unpack128x2 w).`2).
rewrite !unpack128x2E /nttunpack128 //=. split.
+ rewrite tP => i Hi. rewrite !initiE //=. rewrite !initiE //=. rewrite rng_perm_nttunpack128 //.
rewrite /nttunpack /perm_nttunpack128 initiE //= 1:/#.
move:Hi. rewrite rng_iotared => />. do 128!(try (move => Hi; case Hi => />)). 
+ rewrite tP => i Hi. rewrite !initiE //=. rewrite !initiE //=. rewrite rng_perm_nttunpack128 //.
rewrite /nttunpack /perm_nttunpack128 initiE //= 1:/#.
move:Hi. rewrite rng_iotared => />. do 128!(try (move => Hi; case Hi => />)). 
qed.

lemma inj_unpack16x8 (x y : 'a Array128.t) :
  (unpack16x8 x = unpack16x8 y) => (x = y).
rewrite -(unpack16x8K x) -(unpack16x8K y). rewrite !pack16x8K => ->. rewrite unpack16x8K //. qed.

lemma inj_unpack128x2 (x y : 'a Array256.t) :
  (unpack128x2 x = unpack128x2 y) => (x = y).
rewrite -(unpack128x2K x) -(unpack128x2K y). rewrite !pack128x2K => ->. rewrite unpack128x2K //. qed.

lemma nttunpack128_corr_h a :
 hoare[ Jkem_avx2.M(Jkem_avx2.Syscall).__nttunpack128 :
   is16u16x8 a arg ==> is16u16x8 (nttunpack128x16 a) res].
proc.
(*shuffle8*)
pose r0_8 := (shuf8 a.`1 a.`5).`1.
pose r1_8 := (shuf8 a.`2 a.`6).`1.
pose r2_8 := (shuf8 a.`3 a.`7).`1.
pose r3_8 := (shuf8 a.`4 a.`8).`1.
pose r4_8 := (shuf8 a.`1 a.`5).`2.
pose r5_8 := (shuf8 a.`2 a.`6).`2.
pose r6_8 := (shuf8 a.`3 a.`7).`2.
pose r7_8 := (shuf8 a.`4 a.`8).`2.
seq 1 : (is16u16x8 (r0_8,a.`2,a.`3,a.`4,r4_8,a.`6,a.`7,a.`8) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle8_corr_h a.`1 a.`5) => />. auto => />. 
seq 1 : (is16u16x8 (r0_8,r1_8,a.`3,a.`4,r4_8,r5_8,a.`7,a.`8) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle8_corr_h a.`2 a.`6) => />. auto => />.
seq 1 : (is16u16x8 (r0_8,r1_8,r2_8,a.`4,r4_8,r5_8,r6_8,a.`8) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle8_corr_h a.`3 a.`7) => />. auto => />.
seq 1 : (is16u16x8 (r0_8,r1_8,r2_8,r3_8,r4_8,r5_8,r6_8,r7_8) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle8_corr_h a.`4 a.`8) => />. auto => />.
(*shuffle4*)
pose r0_4 := (shuf4 r0_8 r2_8).`1.
pose r1_4 := (shuf4 r1_8 r3_8).`1.
pose r2_4 := (shuf4 r0_8 r2_8).`2.
pose r3_4 := (shuf4 r1_8 r3_8).`2.
pose r4_4 := (shuf4 r4_8 r6_8).`1.
pose r5_4 := (shuf4 r5_8 r7_8).`1.
pose r6_4 := (shuf4 r4_8 r6_8).`2.
pose r7_4 := (shuf4 r5_8 r7_8).`2.
seq 1 : (is16u16x8 (r0_4,r1_8,r2_4,r3_8,r4_8,r5_8,r6_8,r7_8) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle4_corr_h r0_8 r2_8) => />. auto => />.
seq 1 : (is16u16x8 (r0_4,r1_8,r2_4,r3_8,r4_4,r5_8,r6_4,r7_8) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle4_corr_h r4_8 r6_8) => />. auto => />.
seq 1 : (is16u16x8 (r0_4,r1_4,r2_4,r3_4,r4_4,r5_8,r6_4,r7_8) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle4_corr_h r1_8 r3_8) => />. auto => />.
seq 1 : (is16u16x8 (r0_4,r1_4,r2_4,r3_4,r4_4,r5_4,r6_4,r7_4) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle4_corr_h r5_8 r7_8) => />. auto => />.
(*shuffle2*)
pose r0_2 := (shuf2 r0_4 r1_4).`1.
pose r1_2 := (shuf2 r0_4 r1_4).`2.
pose r2_2 := (shuf2 r2_4 r3_4).`1.
pose r3_2 := (shuf2 r2_4 r3_4).`2.
pose r4_2 := (shuf2 r4_4 r5_4).`1.
pose r5_2 := (shuf2 r4_4 r5_4).`2.
pose r6_2 := (shuf2 r6_4 r7_4).`1.
pose r7_2 := (shuf2 r6_4 r7_4).`2.
seq 1 : (is16u16x8 (r0_2,r1_2,r2_4,r3_4,r4_4,r5_4,r6_4,r7_4) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle2_corr_h r0_4 r1_4) => />. auto => />.
seq 1 : (is16u16x8 (r0_2,r1_2,r2_2,r3_2,r4_4,r5_4,r6_4,r7_4) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle2_corr_h r2_4 r3_4) => />. auto => />.
seq 1 : (is16u16x8 (r0_2,r1_2,r2_2,r3_2,r4_2,r5_2,r6_4,r7_4) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle2_corr_h r4_4 r5_4) => />. auto => />.
seq 1 : (is16u16x8 (r0_2,r1_2,r2_2,r3_2,r4_2,r5_2,r6_2,r7_2) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle2_corr_h r6_4 r7_4) => />. auto => />.
(*shuffle1*)
pose r0_1 := (shuf1 r0_2 r4_2).`1.
pose r1_1 := (shuf1 r1_2 r5_2).`1.
pose r2_1 := (shuf1 r2_2 r6_2).`1.
pose r3_1 := (shuf1 r3_2 r7_2).`1.
pose r4_1 := (shuf1 r0_2 r4_2).`2.
pose r5_1 := (shuf1 r1_2 r5_2).`2.
pose r6_1 := (shuf1 r2_2 r6_2).`2.
pose r7_1 := (shuf1 r3_2 r7_2).`2.
seq 1 : (is16u16x8 (r0_1,r1_2,r2_2,r3_2,r4_1,r5_2,r6_2,r7_2) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle1_corr_h r0_2 r4_2) => />. auto => />.
seq 1 : (is16u16x8 (r0_1,r1_1,r2_2,r3_2,r4_1,r5_1,r6_2,r7_2) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle1_corr_h r1_2 r5_2) => />. auto => />.
seq 1 : (is16u16x8 (r0_1,r1_1,r2_1,r3_2,r4_1,r5_1,r6_1,r7_2) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle1_corr_h r2_2 r6_2) => />. auto => />.
seq 1 : (is16u16x8 (r0_1,r1_1,r2_1,r3_1,r4_1,r5_1,r6_1,r7_1) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (avx2_shuffle1_corr_h r3_2 r7_2) => />. auto => />.
(*end*)
auto => /> &m -> -> -> -> -> -> -> ->. 
do 8!(try split; first by
 apply W16u16.wordP => i Hi; rewrite !bits16_W16u16 // Hi //= !of_listE !list_arr16 !initiE //=; rewrite /to_list !nth_mkseq //=; move:Hi; rewrite rng_iotared => />;
 do 16!(try(move => Hi; case Hi => />); first by rewrite /nttunpack128 /perm_nttunpack128 unpack16x8E pack16x8E => />)).
qed.

lemma __nttunpack128_ll: islossless Jkem_avx2.M(Jkem_avx2.Syscall).__nttunpack128 by islossless.

phoare nttunpack128_corr a :
 [ Jkem_avx2.M(Jkem_avx2.Syscall).__nttunpack128 :
   is16u16x8 a arg ==> is16u16x8 (nttunpack128x16 a) res] = 1%r.
conseq __nttunpack128_ll (nttunpack128_corr_h a) => />. qed.

lemma nttunpack_corr_h a :
 hoare[ Jkem_avx2.M(Jkem_avx2.Syscall)._nttunpack : arg = a ==> res = nttunpack a].
proc. sp. 
seq 1 : (rp=a /\ is16u16x8 (nttunpack128x16 (unpack16x8 (unpack128x2 a).`1)) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (nttunpack128_corr_h (unpack16x8 (unpack128x2 a).`1)) => />. auto => />.
do 8!(try split; first by
 apply W16u16.wordP => i Hi; rewrite bits16_W16u16 // Hi //=; rewrite /get256_direct bits16_W32u8 Hi //=; rewrite unpack16x8E unpack128x2E //=; move :Hi; rewrite rng_iotared;
 do 16!(try (move => Hi; case Hi => />); first by rewrite !initiE //= pack2_bits8 //)).
seq 8 : ((unpack128x2 rp).`2 = (unpack128x2 a).`2 /\ (unpack128x2 rp).`1 = (unpack128x2 (nttunpack a)).`1 ).
wp. skip => /> &m -> -> -> -> -> -> -> ->. rewrite nttunpack128x2. rewrite !unpack128x2E => />. split.
+ rewrite tP => j Hj. rewrite !initiE //=. rewrite !initiE //= 1:/#. rewrite !list_arr16 /=.
  do 8!(rewrite set256_directE 1:/#; rewrite get16_set256E //=; rewrite ifF 1:/#; rewrite get16_init16 1:/#; try(rewrite !initiE //=1:/#)). trivial.
+ rewrite tP => j Hj. rewrite !initiE //= 1:/#. rewrite !list_arr16.
  do 7!(rewrite set256_directE 1:/#; rewrite get16_set256E //=; rewrite get16_init16 1:/#; rewrite initiE //= 1:/#).
  rewrite set256_directE 1:/#. rewrite get16_set256E //=. rewrite get16_init16 1:/#. 
  rewrite !bits16_W16u16. rewrite !unpack16x8K. rewrite !of_listE !initE //= /to_list !nth_mkseq_if //=. rewrite rng_perm_nttunpack128 //=. rewrite !unpack16x8E //=. rewrite !initE //=. rewrite /nttunpack128 !initE //=. rewrite !initE //=. rewrite !rng_perm_nttunpack128 //=. smt().
sp. 
seq 1 : ((unpack128x2 rp).`2 = (unpack128x2 a).`2 /\ (unpack128x2 rp).`1 = (unpack128x2 (nttunpack a)).`1 /\ is16u16x8 (nttunpack128x16 (unpack16x8 (unpack128x2 a).`2)) (r0,r1,r2,r3,r4,r5,r6,r7)). auto => />. call (nttunpack128_corr_h (unpack16x8 (unpack128x2 a).`2)) => />. auto => /> &m <- H2.
do 8!(try split; first by
 apply W16u16.wordP => i Hi; rewrite bits16_W16u16 // Hi //=; rewrite /get256_direct bits16_W32u8 Hi //=; rewrite unpack16x8E unpack128x2E //=; move :Hi; rewrite rng_iotared => />;
 do 16!(try (move => Hi; case Hi => />); first by rewrite !initiE //= pack2_bits8 //)).
auto => /> &m H1 H2 -> -> -> -> -> -> -> ->.
apply inj_unpack128x2 => />. rewrite -(unpack128x2K rp{m}) (prod (unpack128x2 rp{m})). rewrite (prod (unpack128x2 (nttunpack a))). 
move :H1 H2. move => -> ->.
rewrite nttunpack128x2 !unpack16x8K !list_arr16 !unpack128x2E !pack128x2E => />. split.
+ rewrite tP => i Hi.
  rewrite !initiE //= 1:/#. rewrite !initiE //=. rewrite rng_perm_nttunpack128 //.
  do 8!(rewrite set256_directE 1:/# get16_set256E //=; rewrite ifF 1:/#; rewrite get16_init16 1:/#; rewrite !initiE //= 1:/#).
  rewrite ifT //=. rewrite /nttunpack128 !initiE //= 1:/#. rewrite !initiE //=. rewrite rng_perm_nttunpack128 1:/#. smt().
+ rewrite tP => i Hi. rewrite !initiE //=. rewrite !initiE //= 1:/#. rewrite rng_perm_nttunpack128 //.
  do 8!(rewrite set256_directE 1:/# get16_set256E //=; rewrite get16_init16 1:/#; rewrite !initiE //= 1:/#).
  rewrite !bits16_W16u16. rewrite !of_listE !initE //= /to_list !nth_mkseq_if //=. rewrite !unpack16x8E //=. rewrite !initE //=. rewrite /nttunpack128 !initE //=. rewrite !initE //=. rewrite !rng_perm_nttunpack128 //= 1..2:/#.
qed.

lemma _nttunpack_ll: islossless Jkem_avx2.M(Jkem_avx2.Syscall)._nttunpack by islossless.

phoare nttunpack_corr a :
 [ Jkem_avx2.M(Jkem_avx2.Syscall)._nttunpack : arg = a ==> res = nttunpack a] = 1%r.
conseq _nttunpack_ll (nttunpack_corr_h a) => />. qed.

hoare matrix_bound_aux : 
    AuxMLKEM.__gen_matrix : true ==> pos_bound2304_cxq res 0 2304 2.
proc. seq 3 : true; 1: by auto.
auto => /> &hr.
rewrite /unlift_matrix /pos_bound2304_cxq => k kb.
rewrite initiE 1:/# /=. rewrite /smod /=; smt(qE Zq.rg_asint).
qed.

hoare matrix_bound : 
    M(Syscall).__gen_matrix : 0 <= to_uint transposed <2  ==> pos_bound2304_cxq res 0 2304 2.
conseq auxgenmatrix_good matrix_bound_aux.
move => /> &1 H H0; exists (seed{1}, to_uint transposed{1} = 1) => /=.
- rewrite W64.to_uint_eq.
  by have [] -> : (to_uint transposed{1} = 0 \/ to_uint transposed{1} = 1) by smt().
by smt().
qed.

equiv genmatrixequiv b :
 Jkem_avx2.M(Jkem_avx2.Syscall)._gen_matrix_avx2 ~ Jkem.M(Jkem.Syscall).__gen_matrix :
    arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3= (W64.of_int (b2i b)) /\ arg{2}.`2 =  (W64.of_int (b2i b))  ==>
    res{1} = nttunpackm res{2} /\
    pos_bound2304_cxq res{1} 0 2304 2 /\
    pos_bound2304_cxq res{2} 0 2304 2.
admitted.
(*
symmetry.
have H : equiv [
 Jkem.M(Jkem.Syscall).__gen_matrix ~ Jkem_avx2.M(Jkem_avx2.Syscall).__gen_matrix  :
   ={arg} ==> res{2} = nttunpackm res{1}].
proc. seq 11 11 : (={r}).
sim (M(Syscall)._shake128_absorb34 ~ Jkem_avx2.M(Jkem_avx2.Syscall)._shake128_absorb34  : true)
    (M(Syscall)._shake128_squeezeblock ~ Jkem_avx2.M(Jkem_avx2.Syscall)._shake128_squeezeblock : true)
     (Jkem_avx2.M(Jkem_avx2.Syscall).__rej_uniform ~ 
     Jkem.M(Jkem.Syscall).__gen_matrix : true).
apply shake128_equiv_absorb.
apply shake128_equiv_squeezeblock.
while {2} (0 <= i{2} <= 3 /\ 
  (forall ki,
      0 <= ki < i{2}*768 => r{2}.[ki] = 
               (nttunpackm r{1}).[ki]) /\
  (forall ki,
      i{2}*768 <= ki < 3*768 => r{2}.[ki] = r{1}.[ki])) (3-i{2});
last by auto => />; smt(Array2304.tP).
move => &1 ?;wp.
while (0 <= j <= 3 /\ 0<=i<3 /\
  (forall ki,
      0 <= ki < i*768 + j*256  => r.[ki] = 
               (nttunpackm r{1}).[ki]) /\
  (forall ki,
      i*768 + j*256 <= ki < 3*768 => r.[ki] = r{1}.[ki])) (3 - j);
last by auto => />; smt(Array2304.tP).
move => ?; wp.
exists* r, i, j; elim *=>  _r _i _j.
call (nttunpack_corr (Array256.init (fun (i_0 : int) => _r.[_i * (3 * 256) + _j * 256 + i_0]))).
auto => />???????. do split; 1,2:smt().
+ move => ki kibl kibh; rewrite initiE 1:/# /=.
  case (_i * 768 + _j * 256 <= ki && ki < _i * 768 + _j * 256 + 256);
      last by smt().
  move => *; rewrite initiE 1:/# /=.
  case (0<= ki < 768).
  + move => *; rewrite /nttunpackv  initiE 1:/# /=.
    case (0<= ki < 256).
    + move => *; rewrite /subarray256 /subarray768.
      congr; last by smt().
      congr; rewrite tP => k kb.
      by rewrite !initiE 1,2:/# /= initiE /#.
    case (256<= ki < 512).
    + move => *; rewrite /subarray256 /subarray768.
      congr; last by smt().
      congr; rewrite tP => k kb.
      by rewrite !initiE 1,2:/# /= initiE /#.
    move => *; rewrite /subarray256 /subarray768.
    congr; last by smt().
    congr; rewrite tP => k kb.
    by rewrite !initiE 1,2:/# /= initiE /#.
  case (768<= ki < 1536).
  + move => /= *; rewrite /nttunpackv  initiE 1:/# /=.
    case (0<= ki -768 < 256).
    + move => *; rewrite /subarray256 /subarray768.
      congr; last by smt().
      congr; rewrite tP => k kb.
      by rewrite !initiE 1,2:/# /= initiE /#.
    case (256<= ki - 768 < 512).
    + move => *; rewrite /subarray256 /subarray768.
      congr; last by smt().
      congr; rewrite tP => k kb.
      by rewrite !initiE 1,2:/# /= initiE /#.
    move => *; rewrite /subarray256 /subarray768.
    congr; last by smt().
    congr; rewrite tP => k kb.
    by rewrite !initiE 1,2:/# /= initiE /#.
  + move => /= *; rewrite /nttunpackv  initiE 1:/# /=.
    case (0<= ki -1536 < 256).
    + move => *; rewrite /subarray256 /subarray768.
      congr; last by smt().
      congr; rewrite tP => k kb.
      by rewrite !initiE 1,2:/# /= initiE /#.
    case (256<= ki - 1536 < 512).
    + move => *; rewrite /subarray256 /subarray768.
      congr; last by smt().
      congr; rewrite tP => k kb.
      by rewrite !initiE 1,2:/# /= initiE /#.
    move => *; rewrite /subarray256 /subarray768.
    congr; last by smt().
    congr; rewrite tP => k kb.
    by rewrite !initiE 1,2:/# /= initiE /#.
+ by smt(Array768.initiE Array2304.initiE).
by smt().
conseq (: _ ==> res{2} = nttunpackm res{1} /\ pos_bound2304_cxq res{1} 0 2304 2). 
+ move => [#] &1 &2  H1 r1 r2 [-> H5]; do split => //.
  rewrite /pos_bound2304_cxq /nttunpackm => k kb.
  rewrite initiE 1:/# /=.
  case (0<=k<768); 1: by
   move => ?;  
    move : (nttunpackv_pred (subarray768 r1 0) (fun a => W16extra.bpos16 a (2*q))); rewrite !allP /=; smt(Array768.initiE).
  case (768<=k<1536); 1: by
   move => ?;  
    move : (nttunpackv_pred (subarray768 r1 1) (fun a => W16extra.bpos16 a (2*q))); rewrite !allP /=; smt(Array768.initiE).
   move => ?;  
    move : (nttunpackv_pred (subarray768 r1 2) (fun a => W16extra.bpos16 a (2*q))); rewrite !allP /=; smt(Array768.initiE).
conseq H matrix_bound => //=. smt(@W64). 
qed.
*)
lemma lift768_nttunpack (v : W16.t Array768.t):
  lift_array768 (nttunpackv v) = nttunpackv (lift_array768 v).
rewrite /lift_array768 /nttunpackv tP => k kb.
rewrite mapiE //= !initiE //=.
case (0<=k <256).
+ move => *; rewrite /subarray256 /nttunpack !initiE //=.
  pose a:=nttunpack_idx.[k].
  rewrite initiE //=. smt(nttunpack_bnd Array256.allP).
  rewrite initiE //=. smt(nttunpack_bnd Array256.allP).
  rewrite mapiE //=. smt(nttunpack_bnd Array256.allP).
case (256<=k <512).
+ move => *; rewrite /subarray256 /nttunpack !initiE //=. smt(). smt().
  pose a:=nttunpack_idx.[k-256].
  rewrite initiE //=. smt(nttunpack_bnd Array256.allP).
  rewrite initiE //=. smt(nttunpack_bnd Array256.allP).
  rewrite mapiE //=. smt(nttunpack_bnd Array256.allP).
move => *; rewrite /subarray256 /nttunpack !initiE //=. smt(). smt().
pose a:=nttunpack_idx.[k-512].
rewrite initiE //=. smt(nttunpack_bnd Array256.allP).
rewrite initiE //=. smt(nttunpack_bnd Array256.allP).
rewrite mapiE //=. smt(nttunpack_bnd Array256.allP).
qed.

module GetNoiseAVX2 = {
  proc _poly_getnoise_eta1_4x(aux3 aux2 aux1 aux0 : W16.t Array256.t,
                               noiseseed : W8.t Array32.t, 
                               nonce : W8.t) : 
      W16.t Array256.t * W16.t Array256.t * W16.t Array256.t * W16.t Array256.t = {
      var n3, n2, n1, n0 : W8.t;
      var aux_3, aux_2, aux_1, aux_0 : W16.t Array256.t;
      n0 <- nonce + W8.of_int 3;
      n1 <- nonce + W8.of_int 2;
      n2 <- nonce + W8.of_int 1;
      n3 <- nonce;
      aux_3 <@Jkem.M(Jkem.Syscall)._poly_getnoise(aux3,noiseseed,n3);
      aux_2 <@Jkem.M(Jkem.Syscall)._poly_getnoise(aux2,noiseseed,n2);
      aux_1 <@Jkem.M(Jkem.Syscall)._poly_getnoise(aux1,noiseseed,n1);
      aux_0 <@Jkem.M(Jkem.Syscall)._poly_getnoise(aux0,noiseseed,n0);
      return (aux_3, aux_2, aux_1, aux_0);
  }

  proc sample_noise_kg(skpv pkpv e : W16.t Array768.t, noiseseed:W8.t Array32.t) : W16.t Array768.t * W16.t Array768.t ={
     var nonce : W8.t;
     var aux_3, aux_2, aux_1, aux_0 : W16.t Array256.t;
                nonce <- (W8.of_int 0);
                (aux_3, aux_2, aux_1,
                aux_0) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => skpv.[0 + i_0])),
                (Array256.init (fun i_0 => skpv.[256 + i_0])),
                (Array256.init (fun i_0 => skpv.[(2 * 256) + i_0])),
                (Array256.init (fun i_0 => e.[0 + i_0])), noiseseed, nonce);
                skpv <- Array768.init
                        (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_3.[i_0-0]
                        else skpv.[i_0]);
                skpv <- Array768.init
                        (fun i_0 => if 256 <= i_0 < 256 + 256
                        then aux_2.[i_0-256] else skpv.[i_0]);
                skpv <- Array768.init
                        (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
                        then aux_1.[i_0-(2 * 256)] else skpv.[i_0]);
                e <- Array768.init
                     (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_0.[i_0-0]
                     else e.[i_0]);
                nonce <- (W8.of_int 4);
                (aux_3, aux_2, aux_1,
                aux_0) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => e.[256 + i_0])),
                (Array256.init (fun i_0 => e.[(2 * 256) + i_0])),
                (Array256.init (fun i_0 => pkpv.[0 + i_0])),
                (Array256.init (fun i_0 => pkpv.[256 + i_0])), noiseseed,
                nonce);
                e <- Array768.init
                     (fun i_0 => if 256 <= i_0 < 256 + 256
                     then aux_3.[i_0-256] else e.[i_0]);
                e <- Array768.init
                     (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
                     then aux_2.[i_0-(2 * 256)] else e.[i_0]);
     return (skpv,e);
  }

  proc samplenoise_enc(sp_0 ep bp : W16.t Array768.t, epp : W16.t Array256.t, noiseseed:W8.t Array32.t) : W16.t Array768.t * W16.t Array768.t * W16.t Array768.t * W16.t Array256.t  = {
     var nonce : W8.t;
     var aux_2, aux_1, aux_0, aux : W16.t Array256.t;
                nonce <- (W8.of_int 0);
                (aux_2, aux_1, aux_0,
                aux) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => sp_0.[0 + i_0])),
                (Array256.init (fun i_0 => sp_0.[256 + i_0])),
                (Array256.init (fun i_0 => sp_0.[(2 * 256) + i_0])),
                (Array256.init (fun i_0 => ep.[0 + i_0])), noiseseed,
                nonce);
                sp_0 <- Array768.init
                        (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_2.[i_0-0]
                        else sp_0.[i_0]);
                sp_0 <- Array768.init
                        (fun i_0 => if 256 <= i_0 < 256 + 256
                        then aux_1.[i_0-256] else sp_0.[i_0]);
                sp_0 <- Array768.init
                        (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
                        then aux_0.[i_0-(2 * 256)] else sp_0.[i_0]);
                ep <- Array768.init
                      (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0]
                      else ep.[i_0]);
                nonce <- (W8.of_int 4);
                (aux_2, aux_1, aux_0,
                aux) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => ep.[256 + i_0])),
                (Array256.init (fun i_0 => ep.[(2 * 256) + i_0])), epp,
                (Array256.init (fun i_0 => bp.[0 + i_0])), noiseseed,
                nonce);
                ep <- Array768.init
                      (fun i_0 => if 256 <= i_0 < 256 + 256
                      then aux_2.[i_0-256] else ep.[i_0]);
                ep <- Array768.init
                      (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
                      then aux_1.[i_0-(2 * 256)] else ep.[i_0]);
                epp <- aux_0;
                bp <- Array768.init
                      (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0]
                      else bp.[i_0]);
                return (sp_0,ep,bp, epp);

  }
}.

(* int value of jth noise coeficient *)
op noise_coef (bytes: W8.t Array128.t) (j: int): int =
 let b = bytes.[j%/2] in b2i b.[j%%2*4] + b2i b.[j%%2*4+1] - (b2i b.[j%%2*4+2] + b2i b.[j%%2*4+3]).

import WArray128.

op B2Ri (bytes: W8.t Array128.t) (j: int): W256.t =
 get256 (WArray128.init8 (fun i => bytes.[i])) j.

lemma bytes_getR (bytes: W8.t Array128.t) (k: int):
 0 <= k && k < 128 =>
 bytes.[k] = B2Ri bytes (k %/ 32) \bits8 (k %% 32).
proof.
move=> Hk; rewrite /B2Ri /get256_direct pack32bE 1:/# initiE 1:/# /=.
by rewrite mulrC -divz_eq /init8 initiE.
qed.

abbrev mask55u256 = VPBROADCAST_8u32 (W32.of_int 1431655765).
abbrev mask33u256 = VPBROADCAST_8u32 (W32.of_int 858993459).
abbrev mask03u256 = VPBROADCAST_8u32 (W32.of_int 50529027).
abbrev mask0Fu256 = VPBROADCAST_8u32 (W32.of_int 252645135).

abbrev mask55u16 = W16.of_int 21845. (* 21845 = 0x5555 *)
abbrev mask33u16 = W16.of_int 13107. (* 13107 = 0x3333 *)
abbrev mask03u16 = W16.of_int 771. (* 771 = 0x0303 *)
abbrev mask0Fu16 = W16.of_int 3855. (* 3855 = 0x0F0F *)

abbrev mask55u8 = W8.of_int 85. (* 85 = 0x55 *)
abbrev mask33u8 = W8.of_int 51. (* 51 = 0x33 *)
abbrev mask03u8 = W8.of_int 3. (* 3 = 0x03 *)
abbrev mask0Fu8 = W8.of_int 15. (* 15 = 0x0F *)

lemma mask55_bits16 k:
 0 <= k < 16 =>
 mask55u256 \bits16 k = mask55u16.
proof.
move=> Hk.
rewrite /VPBROADCAST_8u32.
rewrite bits16_W8u32 Hk //= get_of_list 1:/# /=. 
rewrite (nth_map 0) /=; first smt(size_iota).
have: (k%%2 \in iota_ 0 2) by smt(mem_iota).
by move: (k%%2); rewrite -allP -iotaredE /= W2u16.bits16_div //.
qed.

lemma mask55_bits8 k:
 0 <= k < 32 =>
 mask55u256 \bits8 k = mask55u8.
proof.
move=> Hk.
rewrite /VPBROADCAST_8u32.
rewrite bits8_W8u32 Hk //= get_of_list 1:/# /=. 
rewrite (nth_map 0) /=; first smt(size_iota).
have: (k%%4 \in iota_ 0 4) by smt(mem_iota).
by move: (k%%4); rewrite -allP -iotaredE /= W4u8.bits8_div //.
qed.

lemma mask33_bits16 k:
 0 <= k < 16 =>
 mask33u256 \bits16 k = mask33u16.
proof.
move=> Hk.
rewrite /VPBROADCAST_8u32.
rewrite bits16_W8u32 Hk //= get_of_list 1:/# /=. 
rewrite (nth_map 0) /=; first smt(size_iota).
have: (k%%2 \in iota_ 0 2) by smt(mem_iota).
by move: (k%%2); rewrite -allP -iotaredE /= W2u16.bits16_div //.
qed.

lemma mask33_bits8 k:
 0 <= k < 32 =>
 mask33u256 \bits8 k = mask33u8.
proof.
move=> Hk.
rewrite /VPBROADCAST_8u32.
rewrite bits8_W8u32 Hk //= get_of_list 1:/# /=. 
rewrite (nth_map 0) /=; first smt(size_iota).
have: (k%%4 \in iota_ 0 4) by smt(mem_iota).
by move: (k%%4); rewrite -allP -iotaredE /= W4u8.bits8_div //.
qed.

lemma mask03_bits8 k:
 0 <= k < 32 =>
 mask03u256 \bits8 k = mask03u8.
proof.
move=> Hk.
rewrite /VPBROADCAST_8u32.
rewrite bits8_W8u32 Hk //= get_of_list 1:/# /=. 
rewrite (nth_map 0) /=; first smt(size_iota).
have: (k%%4 \in iota_ 0 4) by smt(mem_iota).
by move: (k%%4); rewrite -allP -iotaredE /= W4u8.bits8_div //.
qed.

lemma mask0F_bits16 k:
 0 <= k < 16 =>
 mask0Fu256 \bits16 k = mask0Fu16.
proof.
move=> Hk.
rewrite /VPBROADCAST_8u32.
rewrite bits16_W8u32 Hk //= get_of_list 1:/# /=. 
rewrite (nth_map 0) /=; first smt(size_iota).
have: (k%%2 \in iota_ 0 2) by smt(mem_iota).
by move: (k%%2); rewrite -allP -iotaredE /= W2u16.bits16_div //.
qed.

lemma mask0F_bits8 k:
 0 <= k < 32 =>
 mask0Fu256 \bits8 k = mask0Fu8.
proof.
move=> Hk.
rewrite /VPBROADCAST_8u32.
rewrite bits8_W8u32 Hk //= get_of_list 1:/# /=. 
rewrite (nth_map 0) /=; first smt(size_iota).
have: (k%%4 \in iota_ 0 4) by smt(mem_iota).
by move: (k%%4); rewrite -allP -iotaredE /= W4u8.bits8_div //.
qed.

lemma VPSRL1_ANDmask55 w k:
 0 <= k < 32 =>
 mask55u256 `&` (VPSRL_16u16 w (W8.of_int 1)) \bits8 k
 = mask55u8 `&` ((w \bits8 k) `>>` (W8.of_int 1)).
proof.
move=> Hk.
rewrite {1}(_:k=2*(k%/2) + (k%%2)); first smt(divz_eq).
rewrite -W256_bits16_bits8 1:/# andb16E /VPSRL_16u16 mapbE 1:/# /=.
rewrite W256_bits16_bits8 1:/# mask55_bits8 1:/#.
apply W8extra.wordP_red. rewrite -allP /=.
have: (k\in iota_ 0 32) by smt(mem_iota).
by move: {Hk} k; rewrite -allP -iotaredE /= !W16.shrwE !W8.shrwE /int_bit /=.
qed.

lemma VPSRL2_ANDmask33 w k:
 0 <= k < 32 =>
 mask33u256 `&` (VPSRL_16u16 w (W8.of_int 2)) \bits8 k
 = mask33u8 `&` ((w \bits8 k) `>>` (W8.of_int 2)).
proof.
move=> Hk.
rewrite {1}(_:k=2*(k%/2) + (k%%2)); first smt(divz_eq).
rewrite -W256_bits16_bits8 1:/# andb16E /VPSRL_16u16 mapbE 1:/# /=.
rewrite W256_bits16_bits8 1:/# mask33_bits8 1:/#.
apply W8extra.wordP_red. rewrite -allP /=.
have: (k\in iota_ 0 32) by smt(mem_iota).
by move: {Hk} k; rewrite -allP -iotaredE /= !W16.shrwE !W8.shrwE /int_bit /=.
qed.

lemma VPSRL4_ANDmask0F w k:
 0 <= k < 32 =>
 VPAND_256 mask0Fu256 (VPSRL_16u16 w (W8.of_int 4)) \bits8 k
 = mask0Fu8 `&` ((w \bits8 k) `>>` (W8.of_int 4)).
proof.
move=> Hk.
rewrite {1}(_:k=2*(k%/2) + (k%%2)); first smt(divz_eq).
rewrite -W256_bits16_bits8 1:/# andb16E /VPSRL_16u16 mapbE 1:/# /=.
rewrite W256_bits16_bits8 1:/# mask0F_bits8 1:/#.
apply W8extra.wordP_red. rewrite -allP /=.
have: (k\in iota_ 0 32) by smt(mem_iota).
by move: {Hk} k; rewrite -allP -iotaredE /= !W16.shrwE !W8.shrwE /int_bit /=.
qed.

lemma to_uint_mask33 (w:W8.t):
 to_uint (mask33u8 `&` w)
 = to_uint w %% 4 + to_uint w %/ 16 %% 4 * 16.
proof.
have ->: mask33u8 = (mask03u8 `<<<` 4) `|` mask03u8.
 apply W8.wordP => k; rewrite -mem_range /range /=. 
 by move: k; apply/List.allP; rewrite -iotaredE /int_bit /=.
rewrite andwC andw_orwDr orw_disjoint.
 apply W8.wordP => k; rewrite -mem_range /range /=. 
 by move: k; apply/List.allP; rewrite -iotaredE /int_bit /=.
have ->: w `&` (mask03u8 `<<<` 4)
        = ((w `>>>` 4) `&` W8.masklsb (6-4)) `<<<` 4.
rewrite -shlw_andmask // shrl_andmaskN // -andwA /=.
congr.
rewrite /max /=.
 apply W8.wordP => k; rewrite -mem_range /range /=. 
 by move: k; apply/List.allP; rewrite -iotaredE /int_bit /=.
have E1: to_uint (w `&` mask03u8) = to_uint w %% 4.
 by rewrite (W8.to_uint_and_mod 2) //.
have /= E2: to_uint ((w `>>>` 4) `&` (masklsb (6-4))%W8 `<<<` 4) = to_uint w %/ 16 %% 4 * 16.
 rewrite /max /= to_uint_shl // (W8.to_uint_and_mod 2) //.
 by rewrite to_uint_shr //= modz_small /#.
rewrite to_uintD_small /=.
 by rewrite E1 E2 /#.
by rewrite E1 E2 /#.
qed.

lemma aux_coef_pos b:
 to_uint (mask33u8 `&` (mask55u8 `&` b  + mask55u8 `&` (b `>>` ru_ones_s)))
 = b2i b.[0] + b2i b.[1] + 16 * (b2i b.[4] + b2i b.[5]).
proof.
rewrite addrC -(mask85_sum b 0) // -(mask85_sum b 2) //= !(W8.andwC mask55u8).
by rewrite to_uint_mask33 /(`>>`) to_uint_shr //= to_uint_shr //= /#.
qed.

lemma aux_coef_neg b:
 to_uint (mask33u8 `&` ((mask55u8 `&` b + mask55u8 `&` (b `>>` ru_ones_s)) `>>` W8.of_int 2))
 = b2i b.[2] + b2i b.[3] + 16 * (b2i b.[6] + b2i b.[7]).
proof.
rewrite to_uint_mask33 to_uint_shr // -divz_mul //= !(W8.andwC mask55u8).
rewrite {1}(_:4=2^2) // (_:64=2^6) // -(mask85_sum b 1) // -(mask85_sum b 3) //=. 
by rewrite to_uint_shr //= to_uint_shr //= /#.
qed.

lemma noise_coef_avx2_aux bytes j:
 3 + noise_coef bytes j
 = let b = bytes.[j%/2] in
   let x = mask55u8 `&` b + mask55u8 `&` (b `>>` W8.one) in
   let y = mask33u8 `&` x + mask33u8 - mask33u8 `&` (x `>>` (W8.of_int 2))in
   to_uint y %/ 2^(j%%2*4) %% 16.
proof.
have LL1: forall (x y z:int), (x + z*y) %% z = x %% z.
 by move=> x1 x2 x3; rewrite -modzDm modzMr /= modz_mod.
have LL2: forall (x y z:int), (x - z*y) %% z = x %% z.
 by move=> x1 x2 x3; rewrite -modzDm -modzNm modzMr /= modz_mod.
move=> /=.
pose b:= bytes.[j %/ 2].
pose x:= mask55u8 `&` b  + mask55u8 `&` (b `>>` ru_ones_s).
case: (j %% 2 = 0) => C.
 rewrite C /=. 
 rewrite -addrA to_uintD /= modz_dvd 1:/#.
 rewrite aux_coef_pos W8.to_uintB.
  by rewrite ule_andw.
 rewrite -modzDm LL1 modzDm aux_coef_neg.
 rewrite Ring.IntID.opprD !addzA LL2 /=.
 by rewrite -modzDml -(modzDmr _ 51) /= modzDml modz_small /#. 
have ->/=: j%%2 = 1 by smt().
rewrite -addrA to_uintD.
rewrite (_:16=2^4) // modz_pow_div //= modz_mod.
rewrite aux_coef_pos W8.to_uintB.
 by rewrite ule_andw.
rewrite aux_coef_neg /= (divz_eq 51 16).
pose X:= (b2i _ + _ + _ + _)%W8.
have /=->: X 
   = b2i b.[0] + b2i b.[1] + (51 %% 16) - (b2i b.[2] + b2i b.[3]) 
     + 16 * (b2i b.[4] + b2i b.[5] + (51 %/ 16) - (b2i b.[6] + b2i b.[7])).
 by rewrite /X /=; ring.
by rewrite mulzC divzMDr // divz_small //= /#.
qed.

lemma noise_coef_avx2 bytes j:
 noise_coef bytes j
 = let b = bytes.[j%/2] in
   let x = mask55u8 `&` b + mask55u8 `&` (b `>>` W8.one) in
   let y = mask33u8 `&` x + mask33u8 - mask33u8 `&` (x `>>` (W8.of_int 2)) in
   if j%%2 = 0
   then to_sint (mask0Fu8 `&` y - mask03u8)
   else to_sint (mask0Fu8 `&` (y `>>` (W8.of_int 4)) - mask03u8).
proof.
have L1: forall x, W8.to_uint x < 128 => W8.to_sint x = to_uint x. 
 by move=> x; rewrite to_sintE /smod /= /#.
rewrite /noise_coef /=.
pose b:= bytes.[j %/ 2].
pose x:= b `&` mask55u8 + (b `>>` ru_ones_s) `&` mask55u8.
pose y:= x `&` mask33u8 + mask33u8 - (x `>>` (W8.of_int 2)) `&` mask33u8.
case: (j %% 2 = 0) => C.
 rewrite C /= andwC W8_to_sintB_small.
  by rewrite !to_sintE  (W8.to_uint_and_mod 4) /smod //= /#.
 rewrite L1 (W8.to_uint_and_mod 4) //= /smod /= 1:/#.
 move: (noise_coef_avx2_aux bytes j) => /=.
 by rewrite C to_sintE /smod => <- /#. 
have C': j %% 2 = 1 by smt().
rewrite C' /= andwC W8_to_sintB_small.
 by rewrite !to_sintE  (W8.to_uint_and_mod 4) /smod //= /#.
rewrite L1 (W8.to_uint_and_mod 4) //= /smod /= 1:/#.
move: (noise_coef_avx2_aux bytes j) => /=.
by rewrite /noise_coef C' to_sintE /smod to_uint_shr //= => <- /#.
qed.

lemma nosmt to_sint8_mod x:
 W8.to_sint x %% W8.modulus = to_uint x.
proof.
rewrite /to_sint /smod.
case: (2 ^ (8 - 1) <= to_uint x) => C.
 rewrite -modzDm -modzNm modzz /= modz_mod.
 rewrite modz_small //.
 by apply JUtils.bound_abs; apply W8.to_uint_cmp.
rewrite modz_small //.
by apply JUtils.bound_abs; apply W8.to_uint_cmp.
qed.

lemma to_sint8K (x:W8.t): W8.of_int (to_sint x) = x.
proof. by rewrite -of_int_mod to_sint8_mod to_uintK. qed.

lemma truncateu128_bits128 (w:W256.t):
 truncateu128 w = w \bits128 0.
proof. by rewrite /truncateu128 to_uint_eq of_uintK bits128_div // of_uintK. qed.

hoare cbd2_avx2_h _bytes:
 Jkem_avx2.M(Jkem_avx2.Syscall).__cbd2: buf=_bytes ==> res = Array256.init (fun k => W16.of_int (noise_coef _bytes k)).
proof.
proc.
sp; simplify.
while (0 <= i <= 4 /\ #{~i}pre /\ List.all (fun k => rp.[k]=W16.of_int (noise_coef _bytes k)) (iota_ 0 (64*i))).
 seq 15: (#pre /\ 
          all (fun k=> if k%%2 = 0
                       then to_sint (f0 \bits8 (k %/ 2)) = noise_coef _bytes (64*i+k)
                       else to_sint (f1 \bits8 (k %/ 2)) = noise_coef _bytes (64*i+k))
              (iota_ 0 64)).
  auto => &m |> ?_ /List.allP H ?; apply/List.allP => k; rewrite mem_iota /= => *.
  case: (k%%2=0) => C1.
   move: (noise_coef_avx2 buf{m} (64*i{m}+k)).
   have ->: (64 * i{m} + k) %% 2 = 0 by smt().
   rewrite /= => ->.
   have:= (bytes_getR buf{m} ((64*i{m}+k)%/2) _); first smt().
   rewrite /B2Ri /= -!divz_mul //=. 
   have ->: (64 * i{m} + k) %/ 64 = i{m}.
    by rewrite (mulzC 64) divzMDl // (divz_small _ 64) 1:/# /=.
   have ->: (64 * i{m} + k) %/ 2 %% 32 = k %/ 2.
    rewrite -(modz_pow_div 2 6 1) //=.
    by rewrite (mulzC 64) modzMDl modz_small /#.
   move => Eb.
   rewrite map2bE 1:/# /= mask0F_bits8 1:/# /=.
   rewrite map2bE 1:/#. beta. 
   rewrite VPSRL2_ANDmask33 1:/#.
   rewrite map2bE 1:/#; beta.
   rewrite map2bE 1:/#; beta.
   rewrite VPSRL1_ANDmask55 1:/#.
   rewrite mask33_bits8 1:/# /=.
   rewrite map2bE 1:/#; beta.
   rewrite VPSRL1_ANDmask55 1:/#.
   rewrite mask33_bits8 1:/# /=.
   rewrite mask55_bits8 1:/# /=.
   rewrite mask03_bits8 1:/# -!Eb.
   by congr.
  have C2: k %% 2 = 1 by smt().
  move: (noise_coef_avx2 buf{m} (64*i{m}+k)).
  have ->: (64 * i{m} + k) %% 2 = 1 by smt().
  rewrite /= => ->.
  have:= (bytes_getR buf{m} ((64*i{m}+k)%/2) _); first smt().
  rewrite /B2Ri /= -!divz_mul //=. 
  have ->: (64 * i{m} + k) %/ 64 = i{m}.
   by rewrite (mulzC 64) divzMDl // (divz_small _ 64) 1:/# /=.
  have ->: (64 * i{m} + k) %/ 2 %% 32 = k %/ 2.
   rewrite -(modz_pow_div 2 6 1) //=.
   by rewrite (mulzC 64) modzMDl modz_small /#.
  move => Eb.
  rewrite map2bE 1:/#; beta.
  rewrite VPSRL4_ANDmask0F 1:/#.
  rewrite map2bE 1:/#; beta.
  rewrite map2bE 1:/#; beta.
  rewrite VPSRL2_ANDmask33 1:/#.
  rewrite map2bE 1:/#; beta.
  rewrite VPSRL1_ANDmask55 1:/#.
  rewrite mask33_bits8 1:/# /=.
  rewrite map2bE 1:/#; beta.
  rewrite VPSRL1_ANDmask55 1:/#.
  rewrite mask33_bits8 1:/# /=.
  rewrite mask55_bits8 1:/# /=.
  rewrite mask03_bits8 1:/# -!Eb.
  by congr.
 seq 10: (#[/:-2]pre /\
          all (fun (k : int) =>
                if k %/ 16 = 0 
                then f0 \bits16 k%%16 = W16.of_int (noise_coef _bytes (64*i+k))
                else if k %/ 16 = 1
                then f2 \bits16 k%%16 = W16.of_int (noise_coef _bytes (64*i+k))
                else if k %/ 16 = 2
                then f1 \bits16 k%%16 = W16.of_int (noise_coef _bytes (64*i+k))
                else f3 \bits16 k%%16 = W16.of_int (noise_coef _bytes (64*i+k)))
              (iota_ 0 64)).
  auto => &m |> ?_ /List.allP IH ?.
  rewrite -{1}iotaredE /= => |> *.
  rewrite -iotaredE /=.
  do 32! (split; first by 
   rewrite /VPMOVSX_16u8_16u16 /VPUNPCKL_32u8 /VPUNPCKL_16u8 /VPUNPCKH_32u8 /VPUNPCKH_16u8 /MOVSX_u16s8 truncateu128_bits128 /interleave_gen /get_lo_2u64 /get_hi_2u64 /= /#).
  do 31! (split; first by
   rewrite /VPMOVSX_16u8_16u16 /VPUNPCKL_32u8 /VPUNPCKL_16u8 /VPUNPCKH_32u8 /VPUNPCKH_16u8 /MOVSX_u16s8 /VEXTRACTI128 /interleave_gen /get_lo_2u64 /get_hi_2u64 /b2i /= /int_bit /= /#).
  by rewrite /VPMOVSX_16u8_16u16 /VPUNPCKL_32u8 /VPUNPCKL_16u8 /VPUNPCKH_32u8 /VPUNPCKH_16u8 /MOVSX_u16s8 /VEXTRACTI128 /interleave_gen /get_lo_2u64 /get_hi_2u64 /b2i /= /int_bit /= /#.
 auto => |> &m ? _ /List.allP IH ? /List.allP H.
 split; first smt().
 rewrite -!NTT_AVX_Fq.PURE 1..4:/#. 
 apply/List.allP => k; rewrite mem_iota /= => |> *.
 rewrite !NTT_AVX_Fq.PUR_get 1..8:/#.
 case: (k %/ 16 = 4 * i{m} + 3) => C1.
  move: (H (k %% 64) _) => /=; first smt(mem_iota).
  rewrite (modz_pow_div 2 6 4) //= C1 (mulzC 4) modzMDl /=.
  rewrite (modz_dvd_pow 4 6 _ 2) //.
  have ->: 64 * i{m} + k %% 64 = k by smt().
  by rewrite /R2C /= Array16.initiE /#.
 case: (k %/ 16 = 4 * i{m} + 2) => C2.
  move: (H (k %% 64) _) => /=; first smt(mem_iota).
  rewrite (modz_pow_div 2 6 4) //= C2 (mulzC 4) modzMDl /=.
  rewrite (modz_dvd_pow 4 6 _ 2) //.
  have ->: 64 * i{m} + k %% 64 = k by smt().
  by rewrite /R2C /= Array16.initiE /#.
 case: (k %/ 16 = 4 * i{m} + 1) => C3.
  move: (H (k %% 64) _) => /=; first smt(mem_iota).
  rewrite (modz_pow_div 2 6 4) //= C3 (mulzC 4) modzMDl /=.
  rewrite (modz_dvd_pow 4 6 _ 2) //.
  have ->: 64 * i{m} + k %% 64 = k by smt().
  by rewrite /R2C /= Array16.initiE /#.
 case: (k %/ 16 = 4 * i{m}) => C4.
  move: (H (k %% 64) _) => /=; first smt(mem_iota).
  rewrite (modz_pow_div 2 6 4) //= C4 modzMr. 
  rewrite (modz_dvd_pow 4 6 _ 2) //.
  have ->: 64 * i{m} + k %% 64 = k by smt().
  by rewrite /R2C /= Array16.initiE /#.
 have ?: k < 64*i{m} by smt().   
 by move: (IH k _) => /=; first smt(mem_iota).
auto => &m |> *.
split; first by rewrite iota0.
move => i rp ???; rewrite (_:i=4) 1:/# /=.
move => /List.allP H.
rewrite tP => k Hk; rewrite (H k _); first smt(mem_iota).
by rewrite initiE /#.
qed.

lemma cbd2_ll : islossless Jkem_avx2.M(Jkem_avx2.Syscall).__cbd2.
proc. inline *. sp; wp. while (true) (4-i). move => z.
auto => /> &hr H. smt().
auto => />i. smt(). qed. 

phoare cbd2_avx2_ph _bytes:
 [Jkem_avx2.M(Jkem_avx2.Syscall).__cbd2: buf=_bytes ==> res = Array256.init (fun k => W16.of_int (noise_coef _bytes k))] = 1%r.
conseq cbd2_ll (cbd2_avx2_h _bytes) => />. qed.

module AuxMLKEMAvx2 = {
  proc cbd2_ref (rp:W16.t Array256.t,buf:W8.t Array128.t) : W16.t Array256.t = {
    var k: int;
    var a, b, c: W8.t;
    var i: W64.t;
    var t: W16.t;
    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 128))) {
      c <- buf.[(W64.to_uint i)];
      a <- c;
      a <- (a `&` (W8.of_int 85));
      c <- (c `>>` (W8.of_int 1));
      c <- (c `&` (W8.of_int 85));
      c <- (c + a);
      a <- c;
      a <- (a `&` (W8.of_int 3));
      b <- c;
      b <- (b `>>` (W8.of_int 2));
      b <- (b `&` (W8.of_int 3));
      a <- (a - b);
      t <- (sigextu16 a);
      rp.[W64.to_uint (W64.of_int 2 * i)] <- t;
      a <- c;
      a <- (a `>>` (W8.of_int 4));
      a <- (a `&` (W8.of_int 3));
      b <- (c `>>` (W8.of_int 6));
      b <- (b `&` (W8.of_int 3));
      a <- (a - b);
      t <- (sigextu16 a);
      rp.[W64.to_uint (W64.of_int 2 * i + W64.one)] <- t;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  proc _poly_getnoise (rp:W16.t Array256.t, seed:W8.t Array32.t,nonce:W8.t) : W16.t Array256.t = {
    var buf:W8.t Array128.t;
    var r;

    buf <- witness;
    buf <@ M(Syscall)._shake256_128_33 (buf,Array33.init (fun i => if i=32 then nonce else seed.[i]));
    r <@ cbd2_ref(rp,buf);
    return r;
  }
  proc __poly_getnoise_eta1_4x(aux3 aux2 aux1 aux0 : W16.t Array256.t,
                               noiseseed : W8.t Array32.t, 
                               nonce : W8.t) : 
      W16.t Array256.t * W16.t Array256.t * W16.t Array256.t * W16.t Array256.t = {
      var n3, n2, n1, n0 : W8.t;
      var aux_3, aux_2, aux_1, aux_0 : W16.t Array256.t;
      n0 <- nonce + W8.of_int 3;
      n1 <- nonce + W8.of_int 2;
      n2 <- nonce + W8.of_int 1;
      n3 <- nonce;
      aux_3 <@ _poly_getnoise(aux3,noiseseed,n3);
      aux_2 <@ _poly_getnoise(aux2,noiseseed,n2);
      aux_1 <@ _poly_getnoise(aux1,noiseseed,n1);
      aux_0 <@ _poly_getnoise(aux0,noiseseed,n0);
      return (aux_3, aux_2, aux_1, aux_0);
  }
}.

hoare cbd2_ref_h _bytes:
 AuxMLKEMAvx2.cbd2_ref: buf=_bytes ==> res = Array256.init (fun k => W16.of_int (noise_coef _bytes k)).
proof.
proc.
while (to_uint i <= 128 /\ #pre /\ List.all (fun k => rp.[k]=W16.of_int (noise_coef _bytes k)) (iota_ 0 (2 * to_uint i))).
 auto => &m |>; rewrite /(\ult) => _ /List.allP IH /= Hi.
 rewrite to_uintD_small /= 1:/#.
 split; first smt().
 apply/List.allP => k; rewrite mem_iota /=; move => [? Hk].
 rewrite to_uintD_small !to_uintM_small /= 1..3:/#.
 case: (k = 2 * to_uint i{m}) => C1.
  rewrite /noise_coef !get_setE 1..2:/# C1 /= ifF 1:/#.
  have ->/=: 2 * to_uint i{m} %/ 2 = to_uint i{m} by smt().
  rewrite -to_sint_eq sigextu16_to_sint (_: 3 = 2^2 -1) // !and_mod //= W8_of_sintK_signed /=; 1: smt(). 
  have ->  /= : 2 * to_uint i{m} %% 2 = 0 by smt().
  by rewrite -parallel_noisesum_low smod_small // /#.
 case: (k = 2 * to_uint i{m}+1) => C2.
  rewrite /noise_coef !get_setE 1..2:/# C2 /=.
  have ->/=: (2 * to_uint i{m} + 1) %/ 2 = to_uint i{m} by smt().
  rewrite -to_sint_eq sigextu16_to_sint (_: 3 = 2^2 -1) // !and_mod //= W8_of_sintK_signed /=; 1: smt(). 
  have ->  /= : (2 * to_uint i{m}+1) %% 2 = 1 by smt().
  by rewrite -parallel_noisesum_high smod_small // /#.
 rewrite !get_setE 1..2:/# C1 C2 /=; apply IH.
 smt(mem_iota).
auto => &m |> *.
split; first by rewrite iota0.
move=> i rp; rewrite /(\ult) => |> ??.
have ->/=: to_uint i = 128 by smt().
rewrite tP => /List.allP H k Hk.
rewrite (H k _) /=.
 smt(mem_iota).
by rewrite initiE //.
qed.

lemma cbd2_ref_ll : islossless AuxMLKEMAvx2.cbd2_ref.
proc. inline*. sp; wp. while (true) (128 - W64.to_uint i). move => z.
auto => /> &hr. rewrite ultE of_uintK //= => H. rewrite to_uintD_small //= /#.
auto => />i H. rewrite ultE of_uintK //= 1:/#. qed.

phoare cbd2_ref_ph _bytes:
 [AuxMLKEMAvx2.cbd2_ref: buf=_bytes ==> res = Array256.init (fun k => W16.of_int (noise_coef _bytes k))] = 1%r.
conseq cbd2_ref_ll (cbd2_ref_h _bytes) => />. qed.

equiv getnoise_split : 
  M(Syscall)._poly_getnoise ~ AuxMLKEMAvx2._poly_getnoise : ={arg} ==> ={res}.
proc; wp; sp => />. 
seq 2 0 : (srp{1}=rp{1} /\ ={buf,rp,seed,nonce} /\ extseed{1}=Array33.init (fun i => if i=32 then nonce{1} else seed{1}.[i]) ).
wp. while{1} (0 <= k{1} <= 32 /\ (forall i, 0 <= i < k{1} => extseed{1}.[i]=seed{1}.[i])) (32-k{1}).
auto => /> &m H1 H2 H3 H4. split. split. smt(). move => i Hi1 Hi2. rewrite get_setE 1:/#. smt(). smt().
auto => /> &m. split. move => i Hi1 Hi2. rewrite !get_out /#. move => extseed k. split. smt(). move => H1 H2 H3 H4. rewrite tP => i Hi. rewrite !initiE 1:/# => />. rewrite get_setE 1:/#. smt().
seq 1 1 : (#pre).
call (_:true). auto => />. sim. auto => />.  
inline *. sim. qed.

equiv getnoise_1x_equiv_avx :
  Jkem_avx2.M(Jkem_avx2.Syscall).__poly_cbd_eta1 ~ AuxMLKEMAvx2.cbd2_ref : ={arg} ==> ={res}.
proc*. inline Jkem_avx2.M(Jkem_avx2.Syscall).__poly_cbd_eta1. rcondt{1} 3. auto => />. sp;wp.
ecall{1} (cbd2_avx2_ph buf{1}) => />.
ecall{2} (cbd2_ref_ph buf{2}) => />.
auto => /> &2. rewrite tP => i Hi. rewrite initiE //=. qed.

equiv getnoise_4x_split : 
  GetNoiseAVX2._poly_getnoise_eta1_4x ~ AuxMLKEMAvx2.__poly_getnoise_eta1_4x : ={arg} ==> ={res}.
proc; wp; sp => />. call getnoise_split => />. call getnoise_split => />. call getnoise_split => />. call getnoise_split => />. auto => />. qed.

equiv getnoiseequiv_avx : 
   Jkem_avx2.M(Jkem_avx2.Syscall)._poly_getnoise_eta1_4x ~ GetNoiseAVX2._poly_getnoise_eta1_4x : ={arg} ==> ={res}.
proc*. 
transitivity{2} { r <@ AuxMLKEMAvx2.__poly_getnoise_eta1_4x(aux3,aux2,aux1,aux0,noiseseed,nonce); } ((r0{1}, r1{1}, r2{1}, r3{1}, seed{1}, nonce{1}) = (aux3{2}, aux2{2}, aux1{2}, aux0{2}, noiseseed{2}, nonce{2}) ==> ={r}) (={aux3,aux2,aux1,aux0,noiseseed,nonce} ==> ={r}); last first.
symmetry. call getnoise_4x_split => />. auto => />. smt(). smt().
(*main proof*)
inline Jkem_avx2.M(Jkem_avx2.Syscall)._poly_getnoise_eta1_4x AuxMLKEMAvx2.__poly_getnoise_eta1_4x AuxMLKEMAvx2._poly_getnoise. swap{2} [30..31] 5. swap{2} [23..24] 10. swap{2} [16..17] 15.
seq 25 30 : (
    r00{1}=rp{2}  /\ Array128.init (fun (i : int) => buf0{1}.[i]) =buf{2}
 /\ r10{1}=rp0{2} /\ Array128.init (fun (i : int) => buf1{1}.[i]) =buf0{2}
 /\ r20{1}=rp1{2} /\ Array128.init (fun (i : int) => buf2{1}.[i]) =buf1{2}
 /\ r30{1}=rp2{2} /\ Array128.init (fun (i : int) => buf3{1}.[i]) =buf2{2}
).
sp => />.
ecall{2} (shake256_33_128 buf2{2} (Array33.init (fun i => if i = 32 then nonce4{2} else seed2{2}.[i]))); wp => />.
ecall{2} (shake256_33_128 buf1{2} (Array33.init (fun i => if i = 32 then nonce3{2} else seed1{2}.[i]))); wp => />.
ecall{2} (shake256_33_128 buf0{2} (Array33.init (fun i => if i = 32 then nonce2{2} else seed0{2}.[i]))); wp => />.
ecall{2} (shake256_33_128 buf{2} (Array33.init (fun i=> if i = 32 then nonce1{2} else seed{2}.[i]))); wp => />.
ecall{1} (shake_squeezenblocks4x state{1} buf0{1} buf1{1} buf2{1} buf3{1}); wp => />.
ecall{1} (shake_absorb4x state{1} (Array33.init (fun i => buf0{1}.[i])) (Array33.init (fun i => buf1{1}.[i])) (Array33.init (fun i => buf2{1}.[i])) (Array33.init (fun i => buf3{1}.[i])) ); wp => />.
auto => /> &2. rewrite shake4x_equiv => />.
rewrite tP => k Hk; rewrite !initiE //= 1..3:/#; rewrite ifF 1:/#; rewrite /get8 /init8 set_neqiE 1:/#; rewrite initiE //= 1:/#; rewrite initiE //= 1:/#; rewrite set256E initiE //= 1:/#; rewrite ifT //; rewrite /get256_direct bits8_W32u8 //=; rewrite ifT //; rewrite initiE //=; rewrite initiE //=.
rewrite tP => k Hk; rewrite !initiE //= 1..3:/#; rewrite ifF 1:/#; rewrite /get8 /init8 set_neqiE 1:/#; rewrite initiE //= 1:/#; rewrite initiE //= 1:/#; rewrite set256E initiE //= 1:/#; rewrite ifT //; rewrite /get256_direct bits8_W32u8 //=; rewrite ifT //; rewrite initiE //=; rewrite initiE //=.
rewrite tP => k Hk; rewrite !initiE //= 1..3:/#; rewrite ifF 1:/#; rewrite /get8 /init8 set_neqiE 1:/#; rewrite initiE //= 1:/#; rewrite initiE //= 1:/#; rewrite set256E initiE //= 1:/#; rewrite ifT //; rewrite /get256_direct bits8_W32u8 //=; rewrite ifT //; rewrite initiE //=; rewrite initiE //=.
rewrite tP => k Hk; rewrite !initiE //= 1..3:/#; rewrite ifF 1:/#; rewrite /get8 /init8 set_neqiE 1:/#; rewrite initiE //= 1:/#; rewrite initiE //= 1:/#; rewrite set256E initiE //= 1:/#; rewrite ifT //; rewrite /get256_direct bits8_W32u8 //=; rewrite ifT //; rewrite initiE //=; rewrite initiE //=.
wp. call getnoise_1x_equiv_avx => />.
wp. call getnoise_1x_equiv_avx => />.
wp. call getnoise_1x_equiv_avx => />.
wp. call getnoise_1x_equiv_avx => />.
auto => />. qed.

lemma polygetnoise_ll : islossless Jkem.M(Jkem.Syscall)._poly_getnoise.
proc. 
while (0 <= to_uint i <= 128) (128 - to_uint i);
  1: by move => z; auto => />;rewrite  ultE /= => &hr ???; rewrite !to_uintD_small /=; smt(to_uint_cmp).
wp; call sha3ll; wp; while (0<=k<=32) (32 -k); 1: by move => z; auto=> /> /#.
auto => /> *; do split; 1:smt(). 
by move => *; rewrite ultE /=; smt().
qed.

equiv getnoiseequiv : 
  Jkem.M(Jkem.Syscall)._poly_getnoise ~Jkem.M(Jkem.Syscall)._poly_getnoise :
   ={arg} ==> ={res} /\
   signed_bound_cxq res{1} 0 256 1.
have H : forall &m a,
   Pr[Jkem.M(Jkem.Syscall)._poly_getnoise(a) @ &m : forall k, 0<=k<256 => -5 < to_sint res.[k] < 5] = 1%r.
+ move => &m a.
  have -> : 1%r = Pr [ CBD2.sample(PRF a.`2 a.`3) @ &m : true].
  + byphoare => //.
    proc; inline *; while (0<=i<=128) (128-i); 1: by move => z; auto => /> /#. 
    by auto => /> /#.
  by byequiv get_noise_sample_noise => //.
have HH0 : hoare [Jkem.M(Jkem.Syscall)._poly_getnoise : true ==> forall k, 0<=k<256 => -5 < to_sint res.[k] < 5].
+ hoare; bypr => //= &m; rewrite Pr[mu_not].
  have -> : Pr[Jkem.M(Jkem.Syscall)._poly_getnoise(rp{m}, seed{m}, nonce{m}) @ &m : true] = 1%r.
  + by byphoare => //; apply polygetnoise_ll.
  smt().
have HHH : equiv [ Jkem.M(Jkem.Syscall)._poly_getnoise ~Jkem.M(Jkem.Syscall)._poly_getnoise : ={arg} ==> ={res} ] by sim.
conseq HHH HH0.
move => *; rewrite /signed_bound_cxq /b16 qE /#.
qed.

import InnerPKE.
lemma mlkem_correct_kg_avx2 mem _pkp _skp  : 
   equiv [Jkem_avx2.M(Jkem_avx2.Syscall).__indcpa_keypair ~ InnerPKE.kg_derand : 
       Glob.mem{1} = mem /\ to_uint pkp{1} = _pkp /\ to_uint skp{1} = _skp /\ 
       randomnessp{1} = coins{2}  /\
       valid_disj_reg _pkp (384*3+32) _skp (384*3)
        ==> 
       touches2 Glob.mem{1} mem _pkp (384*3+32) _skp (384*3) /\
       let (pk,sk) = res{2} in let (t,rho) = pk in
         sk = load_array1152 Glob.mem{1} _skp /\
         t = load_array1152 Glob.mem{1} _pkp  /\
         rho = load_array32 Glob.mem{1} (_pkp+1152)].
proc*.
transitivity {1} {Jkem.M(Jkem.Syscall).__indcpa_keypair(pkp, skp, randomnessp);} 
(={Glob.mem,pkp,skp,randomnessp} /\ 
  Glob.mem{1} = mem /\
    to_uint pkp{1} = _pkp /\
    to_uint skp{1} = _skp /\
    randomnessp{1} = randomnessp{2} /\
    valid_disj_reg _pkp (384 * 3 + 32) _skp (384 * 3) ==> ={Glob.mem}) 
(   Glob.mem{1} = mem /\ to_uint pkp{1} = _pkp /\ to_uint skp{1} = _skp /\ 
       randomnessp{1} = coins{2} /\
       valid_disj_reg _pkp (384*3+32) _skp (384*3)
    ==> 
    touches2 Glob.mem{1} mem _pkp (384*3+32) _skp (384*3) /\
    let (pk, sk) = r{2} in
    let (t, rho) = pk in
        sk = load_array1152 Glob.mem{1} _skp /\
        t = load_array1152 Glob.mem{1} _pkp /\ 
        rho = load_array32 Glob.mem{1} (_pkp + 1152)); 1,2: smt(); 
   last by call(mlkem_correct_kg mem _pkp _skp); auto => />. 

inline{1} 1; inline {2} 1; sim 40 60. 

call (polyvec_tobytes_equiv _pkp).
call (polyvec_tobytes_equiv _skp).
wp;conseq />. smt().
ecall (polyvec_reduce_equiv (lift_array768 pkpv{2})).

have H := polyvec_add2_equiv 2 2 _ _ => //.
ecall (H (lift_array768 pkpv{2}) (lift_array768 e{2})); clear H.
unroll for {1} 36.

sp 3 3.

seq 15 17  : (#pre /\ ={publicseed, noiseseed,e,skpv,pkpv} /\ sskp{2} = skp{1} /\ spkp{2} = pkp{1}); 1: by
 sp; conseq />; sim 2 2; call( sha3equiv); conseq />; sim. 

seq 2 2 : (#pre /\ aa{1} = nttunpackm a{2} /\
           pos_bound2304_cxq aa{1} 0 2304 2 /\
           pos_bound2304_cxq a{2} 0 2304 2); 1: by 
   conseq />; call (genmatrixequiv false); auto => />.

swap {1} [11..12] 2.

seq 10 18 : (#pre  /\
    signed_bound768_cxq skpv{1} 0 768 1 /\
    signed_bound768_cxq e{1} 0 768 1 /\
    signed_bound768_cxq skpv{2} 0 768 1 /\
    signed_bound768_cxq e{2} 0 768 1). 
+ conseq />.
  transitivity {1} { (skpv,e) <@ GetNoiseAVX2.sample_noise_kg(skpv,pkpv,e,noiseseed);} (={noiseseed,skpv,pkpv,e} ==> ={skpv,e}) 
   (
   ((pkp0{2} = pkp{2} /\
    skp0{2} = skp{2} /\
    randomnessp0{2} = randomnessp{2} /\
    pkp0{1} = pkp{1} /\
    skp0{1} = skp{1} /\
    randomnessp0{1} = randomnessp{1} /\
    ={Glob.mem, pkp, skp, randomnessp} /\
    Glob.mem{1} = mem /\
    to_uint pkp{1} = _pkp /\
    to_uint skp{1} = _skp /\
     valid_disj_reg _pkp (384 * 3 + 32) _skp (384 * 3)) /\
   ={publicseed, noiseseed, skpv, pkpv, e}) /\
  aa{1} = nttunpackm a{2} /\ pos_bound2304_cxq aa{1} 0 2304 2 /\ pos_bound2304_cxq a{2} 0 2304 2
   ==> 
    ={skpv, e} /\
  signed_bound768_cxq skpv{1} 0 768 1 /\
  signed_bound768_cxq e{1} 0 768 1 /\ signed_bound768_cxq skpv{2} 0 768 1 /\ signed_bound768_cxq e{2} 0 768 1
  ); 1,2:smt().
  + by inline {2} 1;do 2!(wp; call getnoiseequiv_avx);auto => />. 
  inline {1} 1. inline GetNoiseAVX2._poly_getnoise_eta1_4x.
  wp; do 2!(call{1} (_: true ==> true); 1: by apply polygetnoise_ll).
  do 6!(wp; call  getnoiseequiv); auto => />.
  move => &1 &2 ??????R?; split.
  + by rewrite tP => k kb; rewrite !initiE //= initiE /#.
  move => ?R0?; split.
  + rewrite tP => k kb; rewrite !initiE //= initiE 1:/# /= initiE 1:/# /= /#.
  move => ?R1?????; split.
  + rewrite tP => k kb; rewrite !initiE //= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= /#.
  move => ?R2?; do split. 
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  rewrite /signed_bound768_cxq => x xb /=.
  rewrite !initiE //= fun_if. 
  case (512 <= x && x < 768); 1: by smt().
  move => *; rewrite !initiE //= fun_if. 
  case (256 <= x && x < 512); 1: by smt().
  move => *; rewrite !initiE //= fun_if. 
  by smt().

seq 2 2 : (#{/~skpv{1}}{~e{1}}{~skpv{2}}{~e{2}}pre /\ 
           lift_array768 skpv{1} = nttunpackv (lift_array768 skpv{2}) /\
           lift_array768 e{1} = nttunpackv (lift_array768 e{2}) /\
           pos_bound768_cxq skpv{1} 0 768 2 /\
           pos_bound768_cxq skpv{2} 0 768 2 /\
           pos_bound768_cxq e{1} 0 768 2 /\
           pos_bound768_cxq e{2} 0 768 2); 1: 
 by  conseq />; call (nttequiv); call (nttequiv); auto => /> /#.

(* First ip *)
seq 8 4: (#{/~pkpv{2}}pre /\ 
              lift_array256 (subarray256 pkpv{1} 0) = nttunpack (lift_array256 (subarray256 pkpv{2} 0)) /\
              signed_bound768_cxq pkpv{1} 0 256 2 /\
              signed_bound768_cxq pkpv{2} 0 256 2 /\ i{1} = 1).
wp; call frommontequiv; wp; call pointwiseequiv; auto => />.
move => &1 &2 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE // 1:/# /= kb /= initiE //=. 
+ rewrite /signed_bound768_cxq => k kb; rewrite initiE //=. 
+ rewrite /unpackm /unpackv /=.
  rewrite !initiE // 1:/# /= kb /= initiE //=.
  rewrite fun_if. 
  case (0<=k<256).
  + move => kbb;rewrite /subarray256. 
    move : (nttunpack_pred (Array256.init (fun (k0 : int) => (subarray768 a{2} 0).[256 * 0 + k0])) (fun x => -2*q <= W16.to_sint x < 2*q)).
    rewrite !allP; move => /= [h0 h1]; rewrite  h1. move => *. rewrite initiE //=. smt(Array768.initiE). smt().
  case (256<=k<512).
  + move => kbb;rewrite /subarray256. 
    move : (nttunpack_pred (Array256.init (fun (k0 : int) => (subarray768 a{2} 0).[256 * 1 + k0])) (fun x => -2*q <= W16.to_sint x < 2*q)).
    rewrite !allP; move => /= [h0 h1]; rewrite  h1. move => *. rewrite initiE //=. smt(Array768.initiE). smt(). auto.
  case (512<=k<768).
  + move => kbbb;rewrite /subarray256. 
    move : (nttunpack_pred (Array256.init (fun (k0 : int) => (subarray768 a{2} 0).[256 * 2 + k0])) (fun x => -2*q <= W16.to_sint x < 2*q)).
    rewrite !allP; move => /= [h0 h1]; rewrite  h1. move => *. rewrite initiE //=. smt(Array768.initiE). smt(). auto.
  by smt().
+ move : H10; rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.
+ move : H8; rewrite /pos_bound768_cxq /signed_bound_768_cxq; smt(Array768.initiE).
+ move : H10; rewrite /pos_bound768_cxq /signed_bound_768_cxq; smt(Array768.initiE).

move => H15 H16 H17 H18 H19 r1 r2 H20 H21 H22;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..3: smt(nttunpack_bnd Array256.allP).
  rewrite kb /=. 
  have -> /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  move : H20; rewrite /lift_array256 tP => H20.
  move : (H20 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=;smt(nttunpack_bnd Array256.allP).

move => H23 r3 r4 H24 H25 H26;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite /subarray256 /=.
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite kb /=. 
  have -> /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  move : H24; rewrite /lift_array256 tP => H24.
  move : (H24 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=;smt(nttunpack_bnd Array256.allP).


+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite kb /=. smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite kb /=. smt().

(* Second ip *)

seq 5 4: (#{/~i{1}}pre /\ lift_array256 (subarray256 pkpv{1} 1) = nttunpack (lift_array256 (subarray256 pkpv{2} 1)) /\
              signed_bound768_cxq pkpv{1} 256 512 2 /\
              signed_bound768_cxq pkpv{2} 256 512 2 /\ i{1} = 2).
wp; call frommontequiv; wp; call pointwiseequiv; auto => />.
move => &1 &2 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE //= initiE //= 1:/# ifF 1:/# ifT 1:/# initiE //=. 
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.

move => H18 H19 H20 H21 H22 r1 r2 H23 H24 H25;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifT /=; 1,2: smt(nttunpack_bnd Array256.allP).
  move : H23; rewrite /lift_array256 tP => H23.
  move : (H23 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=;smt(nttunpack_bnd Array256.allP).

move => H26 r3 r4 H27 H28 H29;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite /subarray256 /=.
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifF /=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifF /=; 1..2: smt(nttunpack_bnd Array256.allP).
  move : H15; rewrite /lift_array256 /subarray256 tP => H15.
  move : (H15 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=; 1:smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; smt(nttunpack_bnd Array256.allP).

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !ifF /=. smt(). 
  rewrite !initiE  //=. smt(). smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !ifF /=. smt(). 
  rewrite !initiE  //=. smt(). smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite /subarray256 /=.
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifT /=; 1..2: smt(nttunpack_bnd Array256.allP).
  move : H27; rewrite /lift_array256 /subarray256 tP => H27.
  move : (H27 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=; smt(nttunpack_bnd Array256.allP).

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !initiE  //=. smt(). smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !initiE  //=. smt(). smt().

(* Third ip *)

seq 5 4: (#{/~i{1}}pre /\ lift_array256 (subarray256 pkpv{1} 2) = nttunpack (lift_array256 (subarray256 pkpv{2} 2)) /\
              signed_bound768_cxq pkpv{1} 512 768 2 /\
              signed_bound768_cxq pkpv{2} 512 768 2).
wp; call frommontequiv; wp; call pointwiseequiv; auto => />.
move => &1 &2 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE //= initiE //= 1:/# ifF 1:/# ifF 1:/# initiE //=. 
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.

move => H21 H22 H23 H24 H25 r1 r2 H26 H27 H28;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifT /=; 1,2: smt(nttunpack_bnd Array256.allP).
  move : H26; rewrite /lift_array256 tP => H26.
  move : (H26 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=;smt(nttunpack_bnd Array256.allP).

  move => H29 r3 r4 H30 H31 H32;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite /subarray256 /=.
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifF /=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifF /=; 1..2: smt(nttunpack_bnd Array256.allP).
  move : H15; rewrite /lift_array256 /subarray256 tP => H15.
  move : (H15 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=; 1:smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; smt(nttunpack_bnd Array256.allP).

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !ifF /=. smt(). 
  rewrite !initiE  //=. smt(). smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !ifF /=. smt(). 
  rewrite !initiE  //=. smt(). smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite /subarray256 /=.
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifF /=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifF /=; 1..2: smt(nttunpack_bnd Array256.allP).
  move : H18; rewrite /lift_array256 /subarray256 tP => H18.
  move : (H18 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=; 1:smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; smt(nttunpack_bnd Array256.allP).

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !ifF /=. smt(). 
  rewrite !initiE  //=. smt(). smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !ifF /=. smt(). 
  rewrite !initiE  //=. smt(). smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite /subarray256 /=.
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..2: smt(nttunpack_bnd Array256.allP).
  rewrite !ifT /=; 1..2: smt(nttunpack_bnd Array256.allP).
  move : H30; rewrite /lift_array256 /subarray256 tP => H30.
  move : (H30 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=; smt(nttunpack_bnd Array256.allP).

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !initiE  //=. smt(). smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite !initiE  //=. smt(). smt().


auto => />.

move => &1 &2 ?????????????H1??H2??H3??. 
do split.
+ smt().
+ smt(). 
+ rewrite /lift_array256 /subarray256 tP in H1.
  rewrite /lift_array256 /subarray256 tP in H2.
  rewrite /lift_array256 /subarray256 tP in H3.
  rewrite /nttpackv tP => k kb.
  rewrite initiE //=.
  case (0 <= k && k < 256).
  + move => kbb.
    move : (H1 (nttpack_idx.[k]) _); 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
    pose a:=nttpack_idx.[k].
    rewrite !mapiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    rewrite /nttunpack !initiE //=; 1..2: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    pose b:=nttunpack_idx.[a].
    rewrite !mapiE //=; 1:  smt(nttpack_bnd nttunpack_bnd Array256.allP).
    rewrite /lift_array768 /subarray256 /=.
    pose c := nttpack_idx.[k].
  rewrite /nttunpack initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
  rewrite /nttpack initiE //=.
  rewrite initiE //=. smt(nttpack_bnd nttunpack_bnd Array256.allP).
  rewrite !mapiE //=; 1:  smt(nttpack_bnd Array256.allP).
  have -> : b = k. move : nttunpack_idxK; rewrite /b /a allP; smt(mem_iota).
  smt().
  case (256 <= k && k < 512).
  + move => kbb ?.
    move : (H2 (nttpack_idx.[k-256]) _); 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
    pose a:=nttpack_idx.[k-256].
    rewrite !mapiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    rewrite initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    rewrite /nttunpack initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    pose b:=nttunpack_idx.[a].
    rewrite !mapiE //=; 1:  smt(nttpack_bnd nttunpack_bnd Array256.allP).
    rewrite initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    rewrite /lift_array768 /subarray256 /=.
    pose c := nttpack_idx.[k-256].
  rewrite /nttpack initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
  rewrite initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
  rewrite !mapiE //=; 1:  smt(nttpack_bnd Array256.allP).
  have -> : b = k-256. move : nttunpack_idxK; rewrite /b /a allP; smt(mem_iota).
  smt().

  + move => *.
    move : (H3 (nttpack_idx.[k-512]) _); 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
    pose a:=nttpack_idx.[k-512].
    rewrite !mapiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    rewrite initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    rewrite /nttunpack initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    pose b:=nttunpack_idx.[a].
    rewrite !mapiE //=; 1:  smt(nttpack_bnd nttunpack_bnd Array256.allP).
    rewrite initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP). 
    rewrite /lift_array768 /subarray256 /=.
    pose c := nttpack_idx.[k-512].
  rewrite /nttpack initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
  rewrite initiE //=; 1: smt(nttpack_bnd nttunpack_bnd Array256.allP).
  rewrite !mapiE //=; 1:  smt(nttpack_bnd Array256.allP).
  have -> : b = k-512. move : nttunpack_idxK; rewrite /b /a allP; smt(mem_iota).
  smt().

+  smt(unpackvK).
+ smt().
+ smt().
by smt(unpackvK).
qed.

(***************************************************)

lemma mlkem_correct_enc_0_avx2 mem _ctp _pkp : 
   equiv [Jkem_avx2.M(Jkem_avx2.Syscall).__indcpa_enc_0 ~ InnerPKE.enc_derand: 
     valid_ptr _pkp (384*3 + 32) /\
     valid_ptr _ctp (3*320+128) /\
     Glob.mem{1} = mem /\ 
     msgp{1} = m{2} /\ 
     to_uint sctp{1} = _ctp /\ 
     to_uint pkp{1} = _pkp /\
     noiseseed{1} = coins{2} /\
     pk{2}.`1 = load_array1152 mem _pkp /\
     pk{2}.`2 = load_array32 mem (_pkp + 3*384)
       ==> 
     touches Glob.mem{1} mem _ctp (3*320+128) /\
     let (c1,c2) = res{2} in
     c1 = load_array960 Glob.mem{1} _ctp /\
     c2 = load_array128 Glob.mem{1} (_ctp + 960)
].
proc*.
transitivity {1} {Jkem.M(Jkem.Syscall).__indcpa_enc(sctp,msgp,pkp,noiseseed);} 
(={Glob.mem,msgp,pkp,noiseseed,sctp} /\
  valid_ptr _pkp (384 * 3 + 32) /\
  valid_ptr _ctp (3 * 320 + 128) /\
  Glob.mem{1} = mem /\
  to_uint sctp{1} = _ctp /\
  to_uint pkp{1} = _pkp
   ==> ={Glob.mem,r}) 
( valid_ptr _pkp (384 * 3 + 32) /\
  valid_ptr _ctp (3 * 320 + 128) /\
  Glob.mem{1} = mem /\
  msgp{1} = m{2} /\
  to_uint sctp{1} = _ctp /\
  to_uint pkp{1} = _pkp /\
  noiseseed{1} = coins{2} /\
  pk{2}.`1 = load_array1152 mem _pkp /\ 
  pk{2}.`2 = load_array32 mem (_pkp + 3 * 384)
  ==>
  touches Glob.mem{1} mem _ctp (3*320+128) /\
  let (c1, c2) = r{2} in 
      c1 = load_array960 Glob.mem{1} _ctp /\ 
      c2 = load_array128 Glob.mem{1} (_ctp + 960)); 1,2: smt();  
   last by call(mlkem_correct_enc mem _ctp _pkp); auto => />. 

inline{1} 1; inline {2} 1. wp.

seq 50 59 : (={ctp,Glob.mem} /\
     pos_bound256_cxq v{1} 0 256 2 /\
     pos_bound256_cxq v{2} 0 256 2 /\
    lift_array256 v{1} = lift_array256 v{2} /\ 
    valid_ptr (to_uint ctp{1}) 128); last by
  exists *Glob.mem{1}, (to_uint ctp{1}); elim* => memm _p; call (compressequiv memm _p); auto.

seq 48 57 : (={ctp,Glob.mem} /\
     pos_bound256_cxq v{1} 0 256 2 /\
     pos_bound256_cxq v{2} 0 256 2 /\
     pos_bound768_cxq bp{1} 0 768 2 /\
     pos_bound768_cxq bp{2} 0 768 2 /\
    lift_array256 v{1} = lift_array256 v{2} /\ 
    lift_array768 bp{1} = lift_array768 bp{2} /\ 
    valid_ptr (to_uint ctp{1}) (128+3*320)); last by
  exists *Glob.mem{1}, (to_uint ctp{1}); elim* => memm _p; wp;call (compressequivvec memm _p); auto => />;
   move => *; rewrite !to_uintD_small /= /#.

wp;conseq />.
call (reduceequiv_noperm).
ecall (polyvec_reduce_equiv_noperm (lift_array768 bp{2})).
call (addequiv_noperm 4 2 _ _) => //.
call (addequiv_noperm 2 2 _ _) => //.

have H := polyvec_add2_equiv_noperm 2 2 _ _ => //.
ecall (H (lift_array768 bp{2}) (lift_array768 ep{2})); clear H.


unroll for {1} 39.

swap {1} 3 -2; swap {2} 3 -2; seq 1 1: (#pre /\ ={pkp0} /\ pkp0{2}=pkp{1}); 1: by auto.
sp 3 3.
swap {1} 17 2.
seq 18 17  : (#pre /\ ={publicseed, bp,ep,epp,v,sp_0,k} /\
           s_noiseseed{2} = noiseseed0{2} /\
           pos_bound256_cxq k{1} 0 256 1 /\
           pos_bound256_cxq k{2} 0 256 1 /\
           lift_array768 pkpv{1} = nttunpackv (lift_array768 pkpv{2}) /\
           pos_bound768_cxq pkpv{1} 0 768 2 /\
           pos_bound768_cxq pkpv{2} 0 768 2 /\
           aat{1} = nttunpackm aat{2} /\
           pos_bound2304_cxq aat{1} 0 2304 2 /\
           pos_bound2304_cxq aat{2} 0 2304 2). 
+ call (genmatrixequiv true).
  wp;call frommsgequiv_noperm. conseq />. smt().
  conseq (_: _ ==> lift_array768 pkpv{1} = nttunpackv (lift_array768 pkpv{2}) /\
       pos_bound768_cxq pkpv{1} 0 768 2 /\ pos_bound768_cxq pkpv{2} 0 768 2 /\ ={publicseed,pkp0,bp,ep,epp,v,sp_0,Glob.mem} /\ pkp0{2} = pkp{1} /\ s_noiseseed{2} = noiseseed0{2}).
  auto => /> &2 ????????? rl rr H H0 H1 ????.
  + rewrite tP => k kb.
    move : H; rewrite /lift_array256 tP => H.
    move : (H k kb); rewrite !mapiE //=. 
    move : H0 H1; rewrite /pos_bound256_cxq /bpos16 /= => H0 H1.
    move : (H0 k kb) (H1 k kb).
    rewrite -Zq.eq_incoeff /= qE. 
    move => HH0 HH1; rewrite !modz_small; 1,2: smt( StdOrder.IntOrder.gtr0_norm).    
    move : HH0 HH1; rewrite /to_sint /smod /= => HH0 HH1.
    rewrite  ifF. smt(W16.to_uint_cmp). 
    rewrite  ifF. smt(W16.to_uint_cmp). 
    smt(W16.to_uint_eq).
  seq 12 12 : (#{/~publicseed{2}}post /\ ={publicseed}).
  wp;sp; conseq />.
  call (polyvec_frombytes_equiv).
  auto => />. smt(). 
  conseq />. sim.

sp 2 0.
(* swap {1} [11..12] 2. *)

seq 11 20 : (#{/~bp{1}=bp{2}}pre  /\
    signed_bound768_cxq sp_0{1} 0 768 1 /\
    signed_bound768_cxq ep{1} 0 768 1 /\
    signed_bound_cxq epp{1} 0 256 1 /\
    signed_bound768_cxq sp_0{2} 0 768 1 /\
    signed_bound768_cxq ep{2} 0 768 1 /\ 
    signed_bound_cxq epp{1} 0 256 1).
+ conseq />.
  transitivity {1} { (sp_0,ep,bp,epp) <@ GetNoiseAVX2.samplenoise_enc(sp_0,ep,bp, epp,noiseseed);} (lnoiseseed{1} = noiseseed{2} /\ ={sp_0,ep,bp,epp} ==> ={sp_0,ep,epp}) 
   (
   s_noiseseed{1} = noiseseed0{1} /\
  lnoiseseed{1} = s_noiseseed{1} /\
  (sctp0{2} = sctp{2} /\
   msgp0{2} = msgp{2} /\
   noiseseed0{2} = noiseseed{2} /\
   sctp0{1} = sctp{1} /\
   msgp0{1} = msgp{1} /\
   noiseseed0{1} = noiseseed{1} /\
   (={Glob.mem, msgp, noiseseed, pkp, sctp} /\
    valid_ptr _pkp (384 * 3 + 32) /\
    valid_ptr _ctp (3 * 320 + 128) /\ Glob.mem{1} = mem /\ to_uint sctp{1} = _ctp /\ to_uint pkp{1} = _pkp) /\
   ={pkp0}) /\
  ={publicseed, bp, ep, epp, v, sp_0, k} /\
  s_noiseseed{2} = noiseseed0{2} /\
  pos_bound256_cxq k{1} 0 256 1 /\
  pos_bound256_cxq k{2} 0 256 1 /\
  lift_array768 pkpv{1} = nttunpackv (lift_array768 pkpv{2}) /\
  pos_bound768_cxq pkpv{1} 0 768 2 /\
  pos_bound768_cxq pkpv{2} 0 768 2 /\
  aat{1} = nttunpackm aat{2} /\ pos_bound2304_cxq aat{1} 0 2304 2 /\ pos_bound2304_cxq aat{2} 0 2304 2
   ==> 
    ={ep, epp, sp_0} /\
  signed_bound768_cxq sp_0{1} 0 768 1 /\
  signed_bound768_cxq ep{1} 0 768 1 /\
  signed_bound_cxq epp{1} 0 256 1 /\
  signed_bound768_cxq sp_0{2} 0 768 1 /\ signed_bound768_cxq ep{2} 0 768 1 /\ signed_bound_cxq epp{1} 0 256 1
  ); 1,2:smt().
  + by inline {2} 1;do 2!(wp; call getnoiseequiv_avx);auto => />. 
  inline {1} 1. inline GetNoiseAVX2._poly_getnoise_eta1_4x.
  wp; call{1} (_: true ==> true); 1: by apply polygetnoise_ll.
  do 7!(wp; call  getnoiseequiv); auto => />.
  move => &1 &2 ??????????R?; split.
  + by rewrite tP => k kb; rewrite !initiE //= initiE /#.
  move => ?R0?; split.
  + rewrite tP => k kb; rewrite !initiE //= initiE 1:/# /= initiE 1:/# /= /#.
  move => ?R1?????; split.
  + rewrite tP => k kb; rewrite !initiE //= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= /#.
  move => ?R2???; do split.
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  rewrite /signed_bound768_cxq => x xb /=.
  rewrite !initiE //= fun_if. 
  case (512 <= x && x < 768); 1: by smt().
  move => *; rewrite !initiE //= fun_if. 
  case (256 <= x && x < 512); 1: by smt().
  move => *; rewrite !initiE //= fun_if. 
  by smt().

swap {1} 1 2.
seq 1 1 : (#{/~sp_0{1}}{~sp_0{2}}pre /\ 
           lift_array768 sp_0{1} = nttunpackv (lift_array768 sp_0{2}) /\
           pos_bound768_cxq sp_0{1} 0 768 2 /\
           pos_bound768_cxq sp_0{2} 0 768 2); 1: 
 by  conseq />; call (nttequiv); auto => /> /#.

(* First ip *)

seq 5 2 : (#pre /\ 
              lift_array256 (subarray256 bp{1} 0) = nttunpack (lift_array256 (subarray256 bp{2} 0)) /\
              signed_bound768_cxq bp{1} 0 256 4 /\
              signed_bound768_cxq bp{2} 0 256 2 /\ w{1} = 1).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE // 1:/# /= kb /= initiE //=. 
+ rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#.
+ rewrite /signed_bound768_cxq => k kb; smt(). 
+ rewrite /signed_bound768_cxq => *; rewrite initiE //=; smt().
+ by smt().

move => H15 H16 H17 H18 H19 r1 r2 H20 H21 H22;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..3: smt(nttunpack_bnd Array256.allP).
  rewrite kb /=. 
  have -> /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  move : H20; rewrite /lift_array256 tP => H20.
  move : (H20 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=;smt(nttunpack_bnd Array256.allP).

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite kb /=. smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite kb /=. smt().

(* Second ip *)

seq 3 2: (#{/~w{1}}pre /\ lift_array256 (subarray256 bp{1} 1) = nttunpack (lift_array256 (subarray256 bp{2} 1)) /\
              signed_bound768_cxq bp{1} 256 512 4 /\
              signed_bound768_cxq bp{2} 256 512 2 /\ w{1} = 2).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE //= initiE //= 1:/# ifF 1:/# ifT 1:/# initiE //=. 
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.

move => H18 H19 H20 H21 H22 r1 r2 H23 H24 H25;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..3: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifF 1: /# ifF 1: /# /=. 
  move : H15; rewrite /lift_array256 /subarray256 tP => H15.
  move : (H15 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1, 2: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifT 1: /# ifT 1: /# /=. 
  move : H23; rewrite /lift_array256 tP => H23.
  move : (H23 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

(* Third ip *)

seq 3 2: (#{/~w{1}}pre /\ lift_array256 (subarray256 bp{1} 2) = nttunpack (lift_array256 (subarray256 bp{2} 2)) /\
              signed_bound768_cxq bp{1} 512 768 4 /\
              signed_bound768_cxq bp{2} 512 768 2).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE //= initiE //= 1:/# ifF 1:/# ifF 1:/# initiE //=. 
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.

move => H121 H22 H23 H24 H25 r1 r2 H26 H27 H28;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..3: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifF 1: /# ifF 1: /# /=. 
  move : H15; rewrite /lift_array256 /subarray256 tP => H15.
  move : (H15 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1, 2: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifF 1: /# ifF 1: /# /=. 
  move : H18; rewrite /lift_array256 tP => H18.
  move : (H18 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1, 2: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifT 1: /# ifT 1: /# /=. 
  move : H26; rewrite /lift_array256 tP => H26.
  move : (H26 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

(* Fourth ip *)

seq 1 1: (#{/~v{1}}pre /\ lift_array256 v{1} = nttunpack (lift_array256 v{2}) /\
              signed_bound_cxq v{1} 0 256 4 /\
              signed_bound_cxq v{2} 0 256 2).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23; do split.
+ by rewrite /signed_bound768_cxq => k kb; smt(). 
+ by rewrite /signed_bound768_cxq => k kb; smt(). 
+ by rewrite /signed_bound768_cxq => k kb; smt(). 
+ by rewrite /signed_bound768_cxq => k kb; smt(). 

(* INV NTT!!! *)
seq 1 1 : (#{/~bp{2}}{~bp{1}}pre /\ lift_array768 bp{1} = lift_array768 bp{2} /\ signed_bound768_cxq bp{1} 0 768 2 /\ signed_bound768_cxq bp{2} 0 768 2).
conseq />.  call(invnttequiv). auto => />. move => &1 &2 ???????????????H1??H0??H?????; split.
+ do split; 2,3: by smt().
  rewrite /nttunpackv.
  rewrite tP => k kb; rewrite initiE //=.
  move : H H0 H1; rewrite !tP => H H0 H1.
  case (0 <= k < 256).
  + move => kkb; move : (H1 k kkb). rewrite subliftsub //= => ->. 
    congr;congr.
    rewrite /lift_array256 /subarray256 /lift_array768 tP => i ib.
    rewrite !mapiE //= !initiE //= !mapiE //= 1:/#.
  case (256 <= k < 512).
  + move => nkkb kkb. move : (H0 (k-256) _); 1: smt(). rewrite subliftsub //= 1: /# => ->. 
    congr;congr.
    rewrite /lift_array256 /subarray256 /lift_array768 tP => i ib.
    rewrite !mapiE //= !initiE //= !mapiE //= 1:/#.
  move => *.
  move : (H (k-512) _); 1: smt(). rewrite subliftsub //= 1: /# => ->. 
  congr;congr.
  rewrite /lift_array256 /subarray256 /lift_array768 tP => i ib.
  rewrite !mapiE //= !initiE //= !mapiE //= 1:/#.
  smt().

seq 1 1 : (#{/~v{2}}{~v{1}}pre /\ lift_array256 v{1} = lift_array256 v{2} /\ signed_bound_cxq v{1} 0 256 2 /\ signed_bound_cxq v{2} 0 256 2).
conseq />.  call(polyinvnttequiv). auto => />. smt().

auto => /> /#.
qed.


(***************************************************)

lemma mlkem_correct_enc_1_avx2 mem _pkp : 
   equiv [Jkem_avx2.M(Jkem_avx2.Syscall).__indcpa_enc_1 ~ InnerPKE.enc_derand: 
     valid_ptr _pkp (384*3 + 32) /\
     Glob.mem{1} = mem /\ 
     msgp{1} = m{2} /\ 
     to_uint pkp{1} = _pkp /\
     noiseseed{1} = coins{2} /\
     pk{2}.`1 = load_array1152 mem _pkp /\
     pk{2}.`2 = load_array32 mem (_pkp + 3*384)
       ==> 
     Glob.mem{1} = mem /\
     let (c1,c2) = res{2} in
     c1 = Array960.init (fun i => res{1}.[i]) /\
     c2 = Array128.init (fun i => res{1}.[i+960])
].
proc*.
transitivity {1} { r <@Jkem.M(Jkem.Syscall).__iindcpa_enc(ctp,msgp,pkp,noiseseed);} 
(={Glob.mem,ctp,msgp,pkp,noiseseed} /\
  valid_ptr _pkp (384 * 3 + 32) /\
  Glob.mem{1} = mem /\
  to_uint pkp{1} = _pkp 
   ==> ={Glob.mem,r} /\ Glob.mem{1} = mem) 
( valid_ptr _pkp (384 * 3 + 32) /\
  Glob.mem{1} = mem /\
  msgp{1} = m{2} /\
  to_uint pkp{1} = _pkp /\
  noiseseed{1} = coins{2} /\
  pk{2}.`1 = load_array1152 mem _pkp /\ 
  pk{2}.`2 = load_array32 mem (_pkp + 3 * 384) 
  ==>
  Glob.mem{1} = mem /\
  r{1} = (Array1088.init (fun (i : int) => if 0 <= i && i < 960 then r{2}.`1.[i] else r{2}.`2.[i - 960])));[ by smt() | | | by call(mlkem_correct_ienc mem _pkp); auto => />].
  + move => /> c1 c2. 
    rewrite !tP;split;move => *.
    + by rewrite !initiE // 1:/# /= /#.
    by rewrite !initiE //= !initiE 1:/# /= /#.

inline{1} 1; inline {2} 1. wp.

seq 49 61 : (={ctp0,Glob.mem} /\ Glob.mem{1} = mem /\
     pos_bound256_cxq v{1} 0 256 2 /\
     pos_bound256_cxq v{2} 0 256 2 /\
    lift_array256 v{1} = lift_array256 v{2}); last by
  exists *Glob.mem{1}; elim* => memm; call (compressequiv_1 memm); auto => />; smt(Array1088.tP Array1088.initiE).

seq 47  59 : (={ctp0,Glob.mem} /\ Glob.mem{1} = mem /\
     pos_bound256_cxq v{1} 0 256 2 /\
     pos_bound256_cxq v{2} 0 256 2 /\
     pos_bound768_cxq bp{1} 0 768 2 /\
     pos_bound768_cxq bp{2} 0 768 2 /\
    lift_array256 v{1} = lift_array256 v{2} /\ 
    lift_array768 bp{1} = lift_array768 bp{2}); last 
  exists *Glob.mem{1}; elim* => memm; wp;call (compressequivvec_1 memm); auto => />; smt(Array1088.tP Array1088.initiE).

wp;conseq />.
call (reduceequiv_noperm).
ecall (polyvec_reduce_equiv_noperm (lift_array768 bp{2})).
call (addequiv_noperm 4 2 _ _) => //.
call (addequiv_noperm 2 2 _ _) => //.

have H := polyvec_add2_equiv_noperm 2 2 _ _ => //.
ecall (H (lift_array768 bp{2}) (lift_array768 ep{2})); clear H.


unroll for {1} 39.

swap {1} 3 -2; swap {2} 3 -2; seq 1 1: (#pre /\ ={pkp0} /\ pkp0{2} = pkp{1}); 1: by auto.
sp 3 3.

swap {1} 17 2. (* avoid dealing with stack noise seed *)

seq 18 19  : (#pre /\ ={publicseed, bp,ep,epp,v,sp_0,k} /\ ctp{2} = sctp{2} /\
           s_noiseseed{2} = noiseseed0{2} /\
           pos_bound256_cxq k{1} 0 256 1 /\
           pos_bound256_cxq k{2} 0 256 1 /\
           lift_array768 pkpv{1} = nttunpackv (lift_array768 pkpv{2}) /\
           pos_bound768_cxq pkpv{1} 0 768 2 /\
           pos_bound768_cxq pkpv{2} 0 768 2 /\
           aat{1} = nttunpackm aat{2} /\
           pos_bound2304_cxq aat{1} 0 2304 2 /\
           pos_bound2304_cxq aat{2} 0 2304 2). 
+ call (genmatrixequiv true).
  wp;call frommsgequiv_noperm. conseq />. smt().
  conseq (_: _ ==> lift_array768 pkpv{1} = nttunpackv (lift_array768 pkpv{2}) /\ ctp{2} = sctp{2} /\
       pos_bound768_cxq pkpv{1} 0 768 2 /\ pos_bound768_cxq pkpv{2} 0 768 2 /\ ={publicseed,pkp0,bp,ep,epp,v,sp_0,Glob.mem} /\ pkp0{2} = pkp{1} /\ s_noiseseed{2} = noiseseed0{2}).
  auto => /> &2 ??????? rl rr H H0 H1 ????. 
  + rewrite tP => k kb.
    move : H; rewrite /lift_array256 tP => H.
    move : (H k kb); rewrite !mapiE //=. 
    move : H0 H1; rewrite /pos_bound256_cxq /bpos16 /= => H0 H1.
    move : (H0 k kb) (H1 k kb).
    rewrite -Zq.eq_incoeff /= qE. 
    move => HH0 HH1; rewrite !modz_small; 1,2: smt( StdOrder.IntOrder.gtr0_norm).    
    move : HH0 HH1; rewrite /to_sint /smod /= => HH0 HH1.
    rewrite  ifF. smt(W16.to_uint_cmp). 
    rewrite  ifF. smt(W16.to_uint_cmp). 
    smt(W16.to_uint_eq).

  seq 12 14 : (#{/~publicseed{2}}post /\ ={publicseed}).
  wp;sp; conseq />.
  call (polyvec_frombytes_equiv).
  auto => />. smt().
  conseq />. sim.

sp 2 0.
(* swap {1} [11..12] 2. *)

seq 12 20 : (#{/~bp{1}=bp{2}}pre  /\
    signed_bound768_cxq sp_0{1} 0 768 1 /\
    signed_bound768_cxq ep{1} 0 768 1 /\
    signed_bound_cxq epp{1} 0 256 1 /\
    signed_bound768_cxq sp_0{2} 0 768 1 /\
    signed_bound768_cxq ep{2} 0 768 1 /\ 
    signed_bound_cxq epp{1} 0 256 1).
+ conseq />.
  transitivity {1} { (sp_0,ep,bp,epp) <@ GetNoiseAVX2.samplenoise_enc(sp_0,ep,bp, epp,noiseseed);} (lnoiseseed{1} = noiseseed{2} /\ ={sp_0,ep,bp,epp} ==> ={sp_0,ep,epp}) 
   (
   s_noiseseed{1} = noiseseed0{1} /\
  lnoiseseed{1} = s_noiseseed{1} /\
  (ctp0{2} = ctp{2} /\
   msgp0{2} = msgp{2} /\
   noiseseed0{2} = noiseseed{2} /\
   ctp0{1} = ctp{1} /\
   msgp0{1} = msgp{1} /\
   noiseseed0{1} = noiseseed{1} /\
   (={Glob.mem, msgp, pkp, noiseseed} /\ valid_ptr _pkp (384 * 3 + 32) /\ Glob.mem{1} = mem /\ to_uint pkp{1} = _pkp) /\
   ={pkp0}) /\
  ={publicseed, bp, ep, epp, v, sp_0, k} /\
  s_noiseseed{2} = noiseseed0{2} /\
  pos_bound256_cxq k{1} 0 256 1 /\
  pos_bound256_cxq k{2} 0 256 1 /\
  lift_array768 pkpv{1} = nttunpackv (lift_array768 pkpv{2}) /\
  pos_bound768_cxq pkpv{1} 0 768 2 /\
  pos_bound768_cxq pkpv{2} 0 768 2 /\
  aat{1} = nttunpackm aat{2} /\ pos_bound2304_cxq aat{1} 0 2304 2 /\ pos_bound2304_cxq aat{2} 0 2304 2
   ==> 
    ={ep, epp, sp_0} /\
  signed_bound768_cxq sp_0{1} 0 768 1 /\
  signed_bound768_cxq ep{1} 0 768 1 /\
  signed_bound_cxq epp{1} 0 256 1 /\
  signed_bound768_cxq sp_0{2} 0 768 1 /\ signed_bound768_cxq ep{2} 0 768 1 /\ signed_bound_cxq epp{1} 0 256 1
  ); 1,2:smt().
  + by inline {2} 1;do 2!(wp; call getnoiseequiv_avx);auto => />. 
  inline {1} 1. inline GetNoiseAVX2._poly_getnoise_eta1_4x.
  wp; call{1} (_: true ==> true); 1: by apply polygetnoise_ll.
  do 7!(wp; call  getnoiseequiv); auto => />.
  move => &1 &2 ????????R?; split.
  + by rewrite tP => k kb; rewrite !initiE //= initiE /#.
  move => ?R0?; split.
  + rewrite tP => k kb; rewrite !initiE //= initiE 1:/# /= initiE 1:/# /= /#.
  move => ?R1?????; split.
  + rewrite tP => k kb; rewrite !initiE //= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= /#.
  move => ?R2???; do split.
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  + rewrite /signed_bound768_cxq => x xb /=.
    rewrite !initiE //= fun_if. 
    case (512 <= x && x < 768); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    case (256 <= x && x < 512); 1: by smt().
    move => *; rewrite !initiE //= fun_if. 
    by smt().
  rewrite /signed_bound768_cxq => x xb /=.
  rewrite !initiE //= fun_if. 
  case (512 <= x && x < 768); 1: by smt().
  move => *; rewrite !initiE //= fun_if. 
  case (256 <= x && x < 512); 1: by smt().
  move => *; rewrite !initiE //= fun_if. 
  by smt().

seq 1 1 : (#{/~sp_0{1}}{~sp_0{2}}pre /\ 
           lift_array768 sp_0{1} = nttunpackv (lift_array768 sp_0{2}) /\
           pos_bound768_cxq sp_0{1} 0 768 2 /\
           pos_bound768_cxq sp_0{2} 0 768 2); 1: 
 by  conseq />; call (nttequiv); auto => /> /#.

(* First ip *)

seq 4 2 : (#pre /\ 
              lift_array256 (subarray256 bp{1} 0) = nttunpack (lift_array256 (subarray256 bp{2} 0)) /\
              signed_bound768_cxq bp{1} 0 256 4 /\
              signed_bound768_cxq bp{2} 0 256 2 /\ w{1} = 1).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE // 1:/# /= kb /= initiE //=. 
+ rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#.
+ rewrite /signed_bound768_cxq => k kb; smt(). 
+ rewrite /signed_bound768_cxq => *; rewrite initiE //=; smt().
+ by smt().

move => H15 H16 H17 H18 H19 r1 r2 H20 H21 H22;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..3: smt(nttunpack_bnd Array256.allP).
  rewrite kb /=. 
  have -> /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  move : H20; rewrite /lift_array256 tP => H20.
  move : (H20 k kb). 
  rewrite /nttunpack initiE //= -/a !mapiE //=;smt(nttunpack_bnd Array256.allP).

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite kb /=. smt().

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=. smt().
  rewrite kb /=. smt().

(* Second ip *)

seq 3 2: (#{/~w{1}}pre /\ lift_array256 (subarray256 bp{1} 1) = nttunpack (lift_array256 (subarray256 bp{2} 1)) /\
              signed_bound768_cxq bp{1} 256 512 4 /\
              signed_bound768_cxq bp{2} 256 512 2 /\ w{1} = 2).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE //= initiE //= 1:/# ifF 1:/# ifT 1:/# initiE //=. 
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.

move => H18 H19 H20 H21 H22 r1 r2 H23 H24 H25;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..3: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifF 1: /# ifF 1: /# /=. 
  move : H13; rewrite /lift_array256 /subarray256 tP => H13.
  move : (H13 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1, 2: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifT 1: /# ifT 1: /# /=. 
  move : H23; rewrite /lift_array256 tP => H23.
  move : (H23 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

(* Third ip *)

seq 3 2: (#{/~w{1}}pre /\ lift_array256 (subarray256 bp{1} 2) = nttunpack (lift_array256 (subarray256 bp{2} 2)) /\
              signed_bound768_cxq bp{1} 512 768 4 /\
              signed_bound768_cxq bp{2} 512 768 2).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18; do split.
+ rewrite -lift768_nttunpack. congr.
  rewrite /nttunpackm /nttunpackv tP /= => k kb.
  rewrite !initiE //= initiE //= 1:/# ifF 1:/# ifF 1:/# initiE //=. 
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.
+ by rewrite /signed_bound768_cxq => k kb; rewrite initiE //= /#. 
+ by rewrite /pos_bound768_cxq /signed_bound_768_cxq /#.

move => H121 H22 H23 H24 H25 r1 r2 H26 H27 H28;do split. 
+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1..3: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifF 1: /# ifF 1: /# /=. 
  move : H13; rewrite /lift_array256 /subarray256 tP => H13.
  move : (H13 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1, 2: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifF 1: /# ifF 1: /# /=. 
  move : H16; rewrite /lift_array256 tP => H16.
  move : (H16 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

+ rewrite tP /= => k kb.
  rewrite /lift_array256 /subarray256 /nttunpack !initiE //=. 
  pose a:=nttunpack_idx.[k].
  rewrite !mapiE //=; 1:  smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1: smt(nttunpack_bnd Array256.allP).
  rewrite !initiE //=; 1, 2: smt(nttunpack_bnd Array256.allP).
  have ? /= :  0 <= a && a < 256  by smt(nttunpack_bnd Array256.allP).
  rewrite ifT 1: /# ifT 1: /# /=. 
  move : H26; rewrite /lift_array256 tP => H26.
  move : (H26 k kb). 
  by rewrite /nttunpack initiE //= -/a !mapiE //= initiE //= initiE //=. 

+ rewrite /signed_bound768_cxq /= => k kb; rewrite !initiE  //=; smt().

+ rewrite /signed_bound768_cxq /= => i ib; rewrite !initiE  //=; smt().

(* Fourth ip *)

seq 1 1: (#{/~v{1}}pre /\ lift_array256 v{1} = nttunpack (lift_array256 v{2}) /\
              signed_bound_cxq v{1} 0 256 4 /\
              signed_bound_cxq v{2} 0 256 2).
wp; call pointwiseequiv; auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21; do split.
+ by rewrite /signed_bound768_cxq => k kb; smt(). 
+ by rewrite /signed_bound768_cxq => k kb; smt(). 
+ by rewrite /signed_bound768_cxq => k kb; smt(). 
+ by rewrite /signed_bound768_cxq => k kb; smt(). 

(* INV NTT!!! *)
seq 1 1 : (#{/~bp{2}}{~bp{1}}pre /\ lift_array768 bp{1} = lift_array768 bp{2}  /\ signed_bound768_cxq bp{1} 0 768 2 /\ signed_bound768_cxq bp{2} 0 768 2).
conseq />.  call(invnttequiv). auto => />. move => &1 &2 ?????????????H1??H0??H?????; split.
+ do split; 2,3: by smt().
  rewrite /nttunpackv.
  rewrite tP => k kb; rewrite initiE //=.
  move : H H0 H1; rewrite !tP => H H0 H1.
  case (0 <= k < 256).
  + move => kkb; move : (H1 k kkb). rewrite subliftsub //= => ->. 
    congr;congr.
    rewrite /lift_array256 /subarray256 /lift_array768 tP => i ib.
    rewrite !mapiE //= !initiE //= !mapiE //= 1:/#.
  case (256 <= k < 512).
  + move => nkkb kkb. move : (H0 (k-256) _); 1: smt(). rewrite subliftsub //= 1: /# => ->. 
    congr;congr.
    rewrite /lift_array256 /subarray256 /lift_array768 tP => i ib.
    rewrite !mapiE //= !initiE //= !mapiE //= 1:/#.
  move => *.
  move : (H (k-512) _); 1: smt(). rewrite subliftsub //= 1: /# => ->. 
  congr;congr.
  rewrite /lift_array256 /subarray256 /lift_array768 tP => i ib.
  rewrite !mapiE //= !initiE //= !mapiE //= 1:/#.
  smt().

seq 1 1 : (#{/~v{2}}{~v{1}}pre /\ lift_array256 v{1} = lift_array256 v{2} /\ signed_bound_cxq v{1} 0 256 2 /\ signed_bound_cxq v{2} 0 256 2).
conseq />.  call(polyinvnttequiv). auto => />. smt().

auto => /> /#. 
qed.


lemma mlkem_correct_dec mem _ctp _skp : 
   equiv [Jkem_avx2.M(Jkem_avx2.Syscall).__indcpa_dec_1 ~ InnerPKE.dec : 
     valid_ptr _ctp (3*320+128) /\
     valid_ptr _skp 1152 /\
     Glob.mem{1} = mem /\ 
     to_uint ctp{1} = _ctp /\
     to_uint skp{1} = _skp /\
     sk{2} = load_array1152 Glob.mem{1} _skp /\
     let (c1,c2) = cph{2} in
       c1 = load_array960 Glob.mem{1} _ctp /\
       c2 = load_array128 Glob.mem{1} (_ctp + 960)
       ==> 
     Glob.mem{1} = mem /\
     res{1} = res{2}
].
proc*.
transitivity {1} { r <@Jkem.M(Jkem.Syscall).__indcpa_dec(msgp,ctp,skp);} 
(={Glob.mem,ctp,skp} /\
  valid_ptr _ctp (3*320+128) /\
     valid_ptr _skp 1152 /\
     Glob.mem{1} = mem /\ 
     to_uint ctp{1} = _ctp /\
     to_uint skp{1} = _skp 
   ==> ={Glob.mem,r} /\ Glob.mem{1} = mem) 
( valid_ptr _ctp (3*320+128) /\
     valid_ptr _skp 1152 /\
     Glob.mem{1} = mem /\ 
     to_uint ctp{1} = _ctp /\
     to_uint skp{1} = _skp /\
     sk{2} = load_array1152 Glob.mem{1} _skp /\
     let (c1,c2) = cph{2} in
       c1 = load_array960 Glob.mem{1} _ctp /\
       c2 = load_array128 Glob.mem{1} (_ctp + 960)
       ==> 
     Glob.mem{1} = mem /\
     r{1} = r{2}); 1,2: smt();  
   last by call(mlkem_correct_dec mem _ctp _skp); auto => />. 

inline{1} 1; inline {2} 1.
wp; ecall (tomsgequiv_noperm).
call (reduceequiv_noperm).
call (subequiv_noperm 2 2 _ _) => //.
call(polyinvnttequiv).
call pointwiseequiv.
call(nttequiv).
call (polyvec_frombytes_equiv).
ecall (poly_decompress_equiv mem (_ctp + 3*320)).
wp; call (polyvec_decompress_equiv mem _ctp).
auto => />.
move => &2 ????; split; 1: smt().
move => ????; do split; 1:smt(). 
+ by rewrite to_uintD_small /=; 1: smt().
move => ????? r0 ? rl1 rr1 ???; do split; 1,2: smt().
move => ? rl2 rr2 ???; do split; 1..4: smt().
move => ???? rl3 rr3 ???. do split; smt().
qed.
