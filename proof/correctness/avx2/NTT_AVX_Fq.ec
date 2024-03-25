require import AllCore List IntDiv Ring StdOrder BitEncoding.

require import Fq NTT_Fq NTTAlgebra.

import GFq Rq Correctness.

import Zq IntOrder BitReverse.
import NTTequiv.

from Jasmin require import JModel.
require import Array16 Array128  Array256 Array400.
require import MLKEMFCLib.
require import Array400 WArray32 WArray800 WArray512.


(** DIFFERENT VIEWS ON POLYS *)

(** Poly-to-chunks *)
op pchunk ['a] (p: 'a Array256.t): ('a Array16.t) Array16.t =
 Array16.init (fun i=> Array16.init (fun j=> p.[i*16+j])).

(** Chunks-to-poly *)
op punchunk ['a] (c: ('a Array16.t) Array16.t): 'a Array256.t =
 Array256.init (fun i=>c.[i%/16].[i%%16]).

lemma pchunkK ['a] (p: 'a Array256.t):
 punchunk (pchunk p) = p.
proof.
rewrite /pchunk /punchunk tP /= => i Hi.
rewrite initiE //= initiE //= 1:/#.
by rewrite initiE /#.
qed.

lemma punchunkK ['a] (p: ('a Array16.t) Array16.t):
 pchunk (punchunk p) = p.
proof.
rewrite /pchunk /punchunk tP /= => i Hi.
rewrite initiE //= tP => j Hj.
by rewrite initiE //= initiE /#.
qed.

(** Chunk-to-reg *)
op C2R (c: W16.t Array16.t): W256.t = 
 get256 (WArray32.init16 (fun i=>c.[i])) 0.

(** Reg-to-chunk *)
op R2C (r: W256.t): W16.t Array16.t =
 Array16.init (fun i=> r \bits16 i).

lemma C2RK c:
 R2C (C2R c) = c.
proof.
rewrite /C2R /R2C.
apply Array16.all_eq_eq.
by rewrite /all_eq /get256_direct /= !initiE //= !pack2_bits8.
qed.

lemma R2CK r:
 C2R (R2C r) = r.
proof.
rewrite /C2R /R2C /=.
apply W256.all_eq_eq.
by rewrite /all_eq /get256_direct /= !initiE //= !pack2_bits8.
qed.

(** poly-chunk-i *)
op P2C ['a] (p: 'a Array256.t) (i:int): 'a Array16.t =
 (pchunk p).[i].
(** poly-reg-i *)
op P2R (p: W16.t Array256.t) (i: int): W256.t =
 C2R (P2C p i).

lemma P2R2C p i:
 R2C (P2R p i) = P2C p i.
proof. by rewrite /P2R C2RK. qed.

(** ChunkList-to-poly *)
op CS2P ['a] (l: ('a Array16.t) list): 'a Array256.t =
 punchunk (Array16.of_list witness l).

(** poly-to-chunkList *)
lemma P2CS ['a] (p: 'a Array256.t):
 p = CS2P (map (P2C p) (iotared 0 16)).
proof.
rewrite /CS2P -{1}pchunkK; congr.
by apply Array16.all_eq_eq; rewrite /all_eq /#.
qed.

(** RegList-to-poly *)
op RS2P (l: W256.t list): W16.t Array256.t =
 CS2P (map R2C l).

(** Poly-to-regList *)
lemma P2RS (p: W16.t Array256.t):
 p = RS2P (map (P2R p) (iotared 0 16)).
proof.
rewrite /RS2P /CS2P -{1}pchunkK; congr.
rewrite -map_comp /(\o).
have ->: (fun i=> R2C (P2R p i)) = P2C p.
 by rewrite fun_ext => x; rewrite P2R2C.
by apply Array16.all_eq_eq; rewrite /all_eq /#.
qed.

(** Poly-to-reg extracted code *)
lemma P2RE (p: W16.t Array256.t) (i: int):
 0 <= i < 16 =>
 P2R p i
 = get256_direct (WArray512.init16 (fun i => p.[i])) (32*i).
proof.
move=> Hi.
rewrite /P2R /P2C /pchunk /C2R initiE //=.
rewrite get256E /get256_direct /=; congr.
apply W32u8.Pack.ext_eq => k Hk.
do ! (rewrite initiE 1:/# /=). 
smt().
qed.

(** Poly-update-chunk-i *)
op PUC ['a] (p: 'a Array256.t) (i:int) (x: 'a Array16.t) =
 punchunk (pchunk p).[i <- x].
(** Poly-update-reg-i *)
op PUR (p: W16.t Array256.t) (i: int) (x: W256.t): W16.t Array256.t =
 PUC p i (R2C x).

(** Poly-update-reg extracted code *)
lemma PURE (p: W16.t Array256.t) i x:
 0 <= i < 16 =>
 PUR p i x =
 Array256.init
  (get16 (set256_direct (WArray512.init16 (fun i => p.[i])) (32*i) x)).
proof.
move=> Hi; rewrite /PUR /PUC /punchunk tP => j Hj.
rewrite !initiE 1..2:/# /=.
rewrite get_setE 1:// get16_set256E 1..2:/#.
case: (j %/ 16 = i) => E.
 rewrite -E ifT 1:/#.
 have ->: j - 16 * (j %/ 16) = j %% 16
  by smt(divz_eq).
 by rewrite /r2c initiE 1:/#.
rewrite ifF 1:/# /pchunk initiE 1:/# /=.
rewrite initiE 1:/# /=.
have ->: j %/ 16 * 16 + j %% 16 = j by smt(divz_eq).
by rewrite get16_init16 /#.
qed.

lemma PUR_get p i x k:
  0 <= i < 16 =>
  0 <= k < 256 =>
 (PUR p i x).[k] = if k %/ 16 = i then (R2C x).[k%%16] else p.[k].
proof.
move => |> ????; rewrite /PUR/PUC/pchunk/punchunk /R2C initiE 1:/# /=.
rewrite initiE 1:/# /=.
rewrite get_setE 1://.
case: (k %/ 16 = i) => C.
 by rewrite initiE 1:/# /=.
rewrite initiE 1:/# /= initiE 1:/# /= /#.
qed.

lemma P2C_i ['a] (cs: ('a Array16.t) list) k:
 0 <= k && k < 16 => size cs = 16 =>
 P2C (CS2P cs) k = (nth witness cs k).
proof.
move=> Hk Hcs.
by rewrite /CS2P /P2C punchunkK get_of_list //.
qed.
(*
hint simplify P2C_i.
*)

lemma P2R_i rs k:
 0 <= k && k < 16 => size rs = 16 =>
 P2R (RS2P rs) k = (nth witness rs k).
proof.
move=> Hk Hrs.
rewrite /RS2P /P2R P2C_i //; first by rewrite size_map.
by rewrite (nth_map witness) 1:/# R2CK.
qed.
(*
hint simplify P2R_i.
*)

(* "upd" is equivalent to "put", but intended to be evaluated *)
op upd ['a] (xs: 'a list) n x =
 with xs = "[]" => "[]"
 with xs = (::) y ys => if n=0 then x::ys else y::(upd ys (n-1) x).

lemma nth_upd ['a] (xs: 'a list) d k x i:
 0 <= k < size xs =>
 nth d (upd xs k x) i = if i=k then x else nth d xs i.
proof.
elim: xs k i => //=.
 smt().
move=> y ys IH k i Hk.
case: (i=k) => E.
 case: (k=0) => Ek.
  smt().
 by rewrite ifF 1:/# IH 1:/# ifT 1:/#.
case: (k=0) => Ek.
 smt().
case: (i=0) => Ei //.
by rewrite IH 1:/# ifF 1:/#.
qed.

lemma map_upd ['a 'b] (f: 'a -> 'b) xs k x:
 map f (upd xs k x) = upd (map f xs) k (f x).
proof.
elim: xs k => // y ys IH k /=.
case: (k=0) => E //.
by congr; apply IH.
qed.

lemma PUC_i ['a] cs k (x: 'a Array16.t):
 0 <= k < 16 => size cs = 16 =>
 PUC (CS2P cs) k x = CS2P (upd cs k x).
proof.
move=> Hk Hcs.
rewrite /xs2p /PUC /CS2P; congr.
rewrite tP => i Hi.
case: (i=k) => E.
 by rewrite set_eqiE // get_of_list // nth_upd 1:/# E.
by rewrite set_neqiE // punchunkK !get_of_list // nth_upd 1:/# E.
qed.
(*
hint simplify PUC_i.
*)

lemma PUR_i rs k x:
 0 <= k < 16 => size rs = 16 =>
 PUR (RS2P rs) k x = RS2P (upd rs k x).
proof.
move=> Hk Hrs.
rewrite /PUR /RS2P PUC_i //.
 by rewrite size_map.
by congr; rewrite map_upd.
qed.
(*
hint simplify PUR_i.
*)



(* misc utils *)
lemma rangered (n m :int) :
  range n m = iotared n (m-n).
proof. by rewrite iotaredE /range => />. qed.

lemma ifsplit (b : bool) (t e r : 'a) :
   (b => (t = r)) => (!b => (e = r)) =>
       (if b then t else e) = r 
   by move => Ht Hf; case b; auto.

lemma and_imply2 (p q r : bool) :
  p /\ (p => q => r) => ((p => q) => r).
proof. smt(). qed.

lemma falsify (p : bool) : 
  false => p.
proof. auto. qed.

op perm128 ['a] (p: int list) (a: 'a Array128.t): 'a Array128.t =
 Array128.init (fun i=> a.[nth witness p i]).

op perm_ntt ['a] (p: int list) (a: 'a Array256.t): 'a Array256.t =
  Array256.init (fun i => if i < 128 then a.[nth witness p i] else a.[128 + nth witness p (i-128)]). 


(* Auxiliary proofs on NTTAlgebra *)

abbrev len_avx2S (k:int) = 128 %/ (2^k).
abbrev len_avx2K (k:int) = nth witness [128;64;32;16;8;4;2] k.

lemma len_avx2_equiv (k:int) : 0 <= k < 7 =>
  len_avx2S k = len_avx2K k.
proof.
rewrite -mem_range rangered => />.
do 7!(move => Hk; case Hk => />).
qed.

abbrev zetasctr_avx2S (k:int) = foldl (fun c k => c + 128 %/ len_avx2S k) 0 (range 0 k).
abbrev zetasctr_avx2K (k:int) = nth witness [0;1;3;7;15;31;63] k.

lemma zetasctr_avx2_equiv (k:int) : 0 <= k < 7 =>
  zetasctr_avx2S k = zetasctr_avx2K k.
proof.
rewrite -mem_range rangered => />.
do 7!(try (move => Hk; case Hk => />); first by rewrite rangered => />).
qed.

abbrev block_avx2S k = (128 %/ 2 ^ (7 - k)).
abbrev block_avx2K k = nth witness [1;2;4;8;16;32;64] k.

lemma block_avx2_equiv k : 0 <= k < 7 =>
  block_avx2S k = block_avx2K k.
proof.
  rewrite -mem_range rangered => />.
  do 7!(move => Hk; case Hk => />).
qed.

lemma r_bsrev_ntt_inner_foldl_iE zetas len start r (k:int) :
  0 <= start => start + len*2 <= 256 => 0 <= k <= len =>
  forall i, (r_bsrev_ntt_inner_foldl zetas len start r k).[i] =
  if start <= i < start + k then r.[i] + zetas.[(256 %/ len + start %/ len) %/ 2] * r.[i + len]
  else if start + len <= i < start + len + k then r.[i-len] - zetas.[(256 %/ len + start %/ len) %/ 2] * r.[i]
  else r.[i].  
proof.
move => /> H1 H2. elim/natind:k => />.
(*zero*)
move => n *. rewrite /r_bsrev_ntt_inner_foldl rangered => />. rewrite (_:n=0) => />; smt(). 
(*succ*)
move => n Hn Hrec Hk Hn2 i.
rewrite /r_bsrev_ntt_inner_foldl rangeSr => />. rewrite foldl_map /= foldl_rcons => />.
rewrite /r_bsrev_ntt_inner_foldl foldl_map /r_bsrev_ntt_inner in Hrec => />.
rewrite /r_bsrev_ntt_inner => />. rewrite get_set2_add_mulr_if => />; 1..3: by smt(mem_range).
rewrite !Hrec => />; by smt().
qed.

lemma r_bsrev_ntt_outer_foldl_iE zetas len r (k:int) :
  0 < len =>
  0 <= k <= 128 %/ len =>
  forall i, (r_bsrev_ntt_outer_foldl zetas len r k).[i] =
  if 0 <= i < k*len*2 then
  if i %/ len %% 2 = 0 then r.[i] + zetas.[(256 %/ len + (i %/ len)) %/ 2] * r.[i+len]
  else r.[i-len] - zetas.[(256 %/ len + (i%/len-1)) %/ 2] * r.[i]
  else r.[i].
proof.
move=> Hlen; elim/natind:k => />.
(*zero*)
move => n *. rewrite /r_bsrev_ntt_outer_foldl rangered => />. rewrite (_:n=0) => />; smt(). 
(*succ*)
move => n Hn1 Hrec Hn2 Hn3 i.
rewrite /r_bsrev_ntt_outer_foldl rangeSr => />. rewrite foldl_map /= foldl_rcons => />.
rewrite /r_bsrev_ntt_outer_foldl foldl_map in Hrec => />.
rewrite /r_bsrev_ntt_outer r_bsrev_ntt_inner_foldl_iE => />; 1..3: by smt(). 
rewrite !Hrec => />; 1..3: by smt(). clear Hrec.
case (0 <= i) => />Hi1; last smt().
case (i < n * len * 2) => />Hi2; first smt().
case (i < n * (len*2)+len) => /> Hi3. 
 rewrite (_:i %/ len = n*2) 2:/#.
 by rewrite divz_eqP // /#.
case (i < n * (len * 2) + len + len) => />Hi4; last smt().
rewrite (_:i%/len = n*2+1) => />;1: by smt().
rewrite ifT 1:/# ifF 1:/# /#. 
qed.

(* simpler definition that greatly speeds up proofs below *)
lemma r_avx2_ntt_spec zetas r k : 0 <= k < 7 =>
  r_avx2_ntt zetas r k = Array256.init (fun i =>
    if (i %/ len_avx2K k) %% 2 = 0 then r.[i] + zetas.[zetasctr_avx2K k + i %/ (len_avx2K k*2) + 1]*r.[i+len_avx2K k] else r.[i-len_avx2K k] + (- zetas.[zetasctr_avx2K k + (i-len_avx2K k) %/ (len_avx2K k*2) + 1]*r.[i])
  ).
proof.
move => Hk. rewrite /r_avx2_ntt /r_bsrev_ntt tP => />i Hi1 Hi2.
rewrite r_bsrev_ntt_outer_foldl_iE => />.
  smt(expr_gt0).
 rewrite block_avx2_equiv /#. 
rewrite initiE Hi1 => />.
move :Hk; rewrite -mem_range rangered => />.
do 8!(try (move => Hk; case Hk => />); first by smt()). 
qed.

(* same for invntt *)

abbrev len_inv_avx2S (k:int) = 128 %/ (2^(6-k)).
abbrev len_inv_avx2K (k:int) = nth witness [2;4;8;16;32;64;128] k.

lemma len_inv_avx2_equiv (k:int) : 0 <= k < 7 =>
  len_inv_avx2S k = len_inv_avx2K k.
proof.
rewrite -mem_range rangered => />.
do 7!(move => Hk; case Hk => />).
qed.

abbrev zetasctr_inv_avx2S (k:int) = foldl (fun c k => c + 128 %/ len_inv_avx2S k) 0 (range 0 k).
abbrev zetasctr_inv_avx2K (k:int) = nth witness [0;64;96;112;120;124;126] k.

lemma zetasctr_inv_avx2_equiv (k:int) : 0 <= k < 7 =>
  zetasctr_inv_avx2S k = zetasctr_inv_avx2K k.
proof.
rewrite -mem_range rangered => />.
do 7!(try (move => Hk; case Hk => />); first by rewrite rangered => />).
qed.

abbrev block_inv_avx2S k = (128 %/ 2 ^ (k+1)).
abbrev block_inv_avx2K k = nth witness [64;32;16;8;4;2;1] k.

lemma block_inv_avx2_equiv k : 0 <= k < 7 =>
  block_inv_avx2S k = block_inv_avx2K k.
proof.
  rewrite -mem_range rangered => />.
  do 7!(move => Hk; case Hk => />).
qed.

lemma r_bsrev_invntt_inner_foldl_iE zetas len start r (k:int) :
  0 <= start => start + len*2 <= 256 => 0 <= k <= len =>
  forall i, (r_bsrev_invntt_inner_foldl zetas len start r k).[i] =
  if start <= i < start + k then r.[i] + r.[i + len]
  else if start + len <= i < start + len + k then zetas.[128 + ((-512) + start) %/ (len * 2)] * (r.[i-len] - r.[i])
  else r.[i].
proof.
move => /> H1 H2. elim/natind:k => />.
(*zero*)
move => n *. rewrite /r_bsrev_invntt_inner_foldl rangered => />. rewrite (_:n=0) => />; smt(). 
(*succ*)
move => n Hn Hrec Hk Hn2 i.
rewrite /r_bsrev_invntt_inner_foldl rangeSr => />. rewrite foldl_map /= foldl_rcons => />.
rewrite /r_bsrev_invntt_inner_foldl foldl_map /r_bsrev_invntt_inner in Hrec => />.
rewrite /r_bsrev_invntt_inner => />. rewrite get_set2_mul_addr_if => />; 1..3: by smt(mem_range).
rewrite !Hrec => />; by smt().
qed.

lemma r_bsrev_invntt_outer_foldl_iE zetas len r (k:int) :
  0 < len =>
  0 <= k <= 128 %/ len =>
  forall i, (r_bsrev_invntt_outer_foldl zetas len r k).[i] =
  if 0 <= i < k*len*2 then
  if i %/ len %% 2 = 0 then r.[i] + r.[i + len]
  else zetas.[128 + ((-512) + len*(i%/len-1)) %/ (len * 2)] * (r.[i - len] - r.[i])
  else r.[i].
proof.
move=> Hlen; elim/natind:k => />.
(*zero*)
move => n *. rewrite /r_bsrev_invntt_outer_foldl rangered => />. rewrite (_:n=0) => />; smt(). 
(*succ*)
move => n Hn1 Hrec Hn2 Hn3 i.
rewrite /r_bsrev_invntt_outer_foldl rangeSr => />. rewrite foldl_map /= foldl_rcons => />.
rewrite /r_bsrev_invntt_outer_foldl foldl_map in Hrec => />.
rewrite /r_bsrev_invntt_outer r_bsrev_invntt_inner_foldl_iE => />; 1..3: by smt(). 
rewrite !Hrec => />; 1..3: by smt(). clear Hrec.
case (0 <= i) => />Hi1; last smt().
case (i < n * len * 2) => />Hi2; first smt().
case (i < n * (len*2)+len) => /> Hi3. 
 rewrite (_:i %/ len = n*2) 2:/#.
 by rewrite divz_eqP // /#.
case (i < n * (len * 2) + len + len) => />Hi4; last smt().
by rewrite (_:i%/len = n*2+1) => /> /#.
qed.

(* simpler definition that greatly speeds up proofs below *)
lemma r_avx2_invntt_spec zetas r k : 0 <= k < 7 =>
  r_avx2_invntt zetas r k = Array256.init (fun i =>
    if (i %/ len_inv_avx2K k) %% 2 = 0 then r.[i] + r.[i + len_inv_avx2K k] else zetas.[zetasctr_inv_avx2K k + len_inv_avx2K k * (i%/len_inv_avx2K k - 1) %/ (len_inv_avx2K k*2)] * (r.[i - len_inv_avx2K k] - r.[i])
  ).
proof.
move => Hk. rewrite /r_avx2_invntt /r_bsrev_invntt tP => />i Hi1 Hi2.
rewrite r_bsrev_invntt_outer_foldl_iE => />.
  smt(expr_gt0).
 rewrite block_inv_avx2_equiv /#. 
rewrite initiE Hi1 => />.
move :Hk; rewrite -mem_range rangered => />.
do 8!(try (move => Hk; case Hk => />); first by smt()). 
qed.

lemma r_avx2_invntt_post_spec zetas r :
  r_avx2_invntt_post zetas r = Array256.init (fun i => r.[i] * zetas.[127]).
proof.
rewrite /r_avx2_invntt_post /r_bsrev_invntt_post_foldl /r_bsrev_invntt_post => />.
pose upd := (fun (i:int) x => x * zetas.[127]).
rewrite (_:(fun (i : int) => r.[i] * zetas.[127]) = (fun (i : int) => upd i r.[i]) ) => />. 
rewrite -foldl_upd_range => />. qed.

(* NTT AVX intermediate implementation *)

(*theory NTT_AVX_Fq.*)

op shuffle8 ['a] (r1 r2: 'a Array16.t): 'a Array16.t * 'a Array16.t =
  ( Array16.init (fun i => if 0 <= i < 8 then r1.[i%%8] else r2.[i%%8])
  , Array16.init (fun i => if 0 <= i < 8 then r1.[i%%8+8] else r2.[i%%8+8])
  ) axiomatized by shuffle8E.

op shuffle4 ['a] (r1 r2: 'a Array16.t): 'a Array16.t * 'a Array16.t =
  ( Array16.init (fun i =>
    if 0 <= i < 4 then r1.[i%%4]
    else if 4 <= i < 8 then r2.[i%%4]
    else if 8 <= i < 12 then r1.[i%%4+8]
    else r2.[i%%4+8]
    )
  , Array16.init (fun i =>
    if 0 <= i < 4 then r1.[i%%4+4]
    else if 4 <= i < 8 then r2.[i%%4+4]
    else if 8 <= i < 12 then r1.[i%%4+12]
    else r2.[i%%4+12]
    )
  ) axiomatized by shuffle4E.

op shuffle2 ['a] (r1 r2: 'a Array16.t): 'a Array16.t * 'a Array16.t =
  ( Array16.init (fun i =>
    if 0 <= i < 2 then r1.[i%%2]
    else if 2 <= i < 4 then r2.[i%%2]
    else if 4 <= i < 6 then r1.[i%%2+4]
    else if 6 <= i < 8 then r2.[i%%2+4]
    else if 8 <= i < 10 then r1.[i%%2+8]
    else if 10 <= i < 12 then r2.[i%%2+8]
    else if 12 <= i < 14 then r1.[i%%2+12]
    else r2.[i%%2+12]
    )
  , Array16.init (fun i =>
    if 0 <= i < 2 then r1.[i%%2+2]
    else if 2 <= i < 4 then r2.[i%%2+2]
    else if 4 <= i < 6 then r1.[i%%2+6]
    else if 6 <= i < 8 then r2.[i%%2+6]
    else if 8 <= i < 10 then r1.[i%%2+10]
    else if 10 <= i < 12 then r2.[i%%2+10]
    else if 12 <= i < 14 then r1.[i%%2+14]
    else r2.[i%%2+14]
    )
  ) axiomatized by shuffle2E.

op shuffle1 ['a] (r1 r2: 'a Array16.t): 'a Array16.t * 'a Array16.t =
  ( Array16.of_list witness [r1.[0];r2.[0];r1.[2];r2.[2];r1.[4];r2.[4];r1.[6];r2.[6];r1.[8];r2.[8];r1.[10];r2.[10];r1.[12];r2.[12];r1.[14];r2.[14]]
  , Array16.of_list witness [r1.[1];r2.[1];r1.[3];r2.[3];r1.[5];r2.[5];r1.[7];r2.[7];r1.[9];r2.[9];r1.[11];r2.[11];r1.[13];r2.[13];r1.[15];r2.[15]]
  ) axiomatized by shuffle1E.

(* These are imperative specifications of the NTT algorithms whose control
   structure matches what is implemented.  *)

(* permutation that nttpack128 applies to the input indexes *)
op perm_nttpack128 : int list =
  [0; 16; 32; 48; 64; 80; 96; 112; 1; 17; 33; 49; 65; 81; 97; 113;
   2; 18; 34; 50; 66; 82; 98; 114; 3; 19; 35; 51; 67; 83; 99; 115;
   4; 20; 36; 52; 68; 84; 100; 116; 5; 21; 37; 53; 69; 85; 101; 117;
   6; 22; 38; 54; 70; 86; 102; 118; 7; 23; 39; 55; 71; 87; 103; 119;
   8; 24; 40; 56; 72; 88; 104; 120; 9; 25; 41; 57; 73; 89; 105; 121;
   10; 26; 42; 58; 74; 90; 106; 122; 11; 27; 43; 59; 75; 91; 107; 123;
   12; 28; 44; 60; 76; 92; 108; 124; 13; 29; 45; 61; 77; 93; 109; 125;
   14; 30; 46; 62; 78; 94; 110; 126; 15; 31; 47; 63; 79; 95; 111; 127]
  axiomatized by perm_nttpack128E.

op nttpack128 ['a] (rp : 'a Array128.t) : 'a Array128.t = perm128 perm_nttpack128 rp.

(* permutation that nttunpack128 applies to the input indexes *)
op perm_nttunpack128 : int list =
  [0;8;16;24;32;40;48;56;64;72;80;88;96;104;112;120;
  1;9;17;25;33;41;49;57;65;73;81;89;97;105;113;121;
  2;10;18;26;34;42;50;58;66;74;82;90;98;106;114;122;
  3;11;19;27;35;43;51;59;67;75;83;91;99;107;115;123;
  4;12;20;28;36;44;52;60;68;76;84;92;100;108;116;124;
  5;13;21;29;37;45;53;61;69;77;85;93;101;109;117;125;
  6;14;22;30;38;46;54;62;70;78;86;94;102;110;118;126;
  7;15;23;31;39;47;55;63;71;79;87;95;103;111;119;127]
  axiomatized by perm_nttunpack128E.

op nttunpack128 ['a] (rp : 'a Array128.t) : 'a Array128.t = perm128 perm_nttunpack128 rp.

module NTT_AVX = {

(*proc __nttpack128(r0 r1 r2 r3 r4 r5 r6 r7: Fq Array16.t): Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t = {
  
  var r0a,r1a,r2a,r3a,r4a,r5a,r6a,r7a : Fq Array16.t;
  var r0b,r1b,r2b,r3b,r4b,r5b,r6b,r7b : Fq Array16.t;
  var r0c,r1c,r2c,r3c,r4c,r5c,r6c,r7c : Fq Array16.t;
  var r0d,r1d,r2d,r3d,r4d,r5d,r6d,r7d : Fq Array16.t;

  (r0a, r1a) <- shuffle1 r0 r1;
  (r2a, r3a) <- shuffle1 r2 r3;
  (r4a, r5a) <- shuffle1 r4 r5;
  (r6a, r7a) <- shuffle1 r6 r7;

  (r0b, r2b) <- shuffle2 r0a r2a;
  (r4b, r6b) <- shuffle2 r4a r6a;
  (r1b, r3b) <- shuffle2 r1a r3a;
  (r5b, r7b) <- shuffle2 r5a r7a;

  (r0c, r4c) <- shuffle4 r0b r4b;
  (r1c, r5c) <- shuffle4 r1b r5b;
  (r2c, r6c) <- shuffle4 r2b r6b;
  (r3c, r7c) <- shuffle4 r3b r7b;

  (r0d, r1d) <- shuffle8 r0c r1c;
  (r2d, r3d) <- shuffle8 r2c r3c;
  (r4d, r5d) <- shuffle8 r4c r5c;
  (r6d, r7d) <- shuffle8 r6c r7c;

  return (r0d, r2d, r4d, r6d, r1d, r3d, r5d, r7d);
}

proc __nttunpack128(r0 r1 r2 r3 r4 r5 r6 r7: Fq Array16.t): Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t * Fq Array16.t = {
  
  var r0a,r1a,r2a,r3a,r4a,r5a,r6a,r7a : Fq Array16.t;
  var r0b,r1b,r2b,r3b,r4b,r5b,r6b,r7b : Fq Array16.t;
  var r0c,r1c,r2c,r3c,r4c,r5c,r6c,r7c : Fq Array16.t;
  var r0d,r1d,r2d,r3d,r4d,r5d,r6d,r7d : Fq Array16.t;

  (r0a, r4a) <- shuffle8 r0 r4;
  (r1a, r5a) <- shuffle8 r1 r5;
  (r2a, r6a) <- shuffle8 r2 r6;
  (r3a, r7a) <- shuffle8 r3 r7;

  (r0b, r2b) <- shuffle4 r0a r2a;
  (r4b, r6b) <- shuffle4 r4a r6a;
  (r1b, r3b) <- shuffle4 r1a r3a;
  (r5b, r7b) <- shuffle4 r5a r7a;

  (r0c, r1c) <- shuffle2 r0b r1b;
  (r2c, r3c) <- shuffle2 r2b r3b;
  (r4c, r5c) <- shuffle2 r4b r5b;
  (r6c, r7c) <- shuffle2 r7b r7b;

  (r0d, r4d) <- shuffle1 r0c r4c;
  (r1d, r5d) <- shuffle1 r1c r5c;
  (r2d, r6d) <- shuffle1 r2c r6c;
  (r3d, r7d) <- shuffle1 r3c r7c;

  return (r0d, r4d, r1d, r5d, r2d, r6d, r3d, r7d);
}*)

proc __butterfly64x(rl0t rl1t rl2t rl3t rh0t rh1t rh2t rh3t z0 z1: coeff Array16.t) : coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t = {

  var rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3;

  rh0 <- Array16.init (fun i => rl0t.[i] + -(z0.[i] * rh0t.[i]));
  rl0 <- Array16.init (fun i => rl0t.[i] + z0.[i] * rh0t.[i]);
  
  rh1 <- Array16.init (fun i => rl1t.[i] + -(z0.[i] * rh1t.[i]));
  rl1 <- Array16.init (fun i => rl1t.[i] + z0.[i] * rh1t.[i]);
  
  rh2 <- Array16.init (fun i => rl2t.[i] + -(z1.[i] * rh2t.[i]));
  rl2 <- Array16.init (fun i => rl2t.[i] + z1.[i] * rh2t.[i]);
  
  rh3 <- Array16.init (fun i => rl3t.[i] + -(z1.[i] * rh3t.[i]));
  rl3 <- Array16.init (fun i => rl3t.[i] + z1.[i] * rh3t.[i]);
  
  return (rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3);
}

(* This procedure handles the iteration where the butterflies touch both halves
   of the 256-position array. For all the other rounds, the implementation does
   roughly the same process on each 128 position half. See loop *)

proc __ntt_level0 (rp : coeff Array256.t) : coeff Array256.t = {

  var  zeta1 : coeff Array16.t;
  var r0, r1, r2, r3, r4, r5, r6, r7 : coeff Array16.t;
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b : coeff Array16.t;
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;

  (r0,r1,r2,r3,r0b,r1b,r2b,r3b) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r4,r5,r6,r7,r4b,r5b,r6b,r7b) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);

  zeta1 <- Array16.init (fun i => incoeff 1729);

  (r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a) <@ 
      __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta1, zeta1);

  (r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c) <@ 
      __butterfly64x(r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b, zeta1, zeta1);
      
  rp <- CS2P [r0a;r1a;r2a;r3a;r0c;r1c;r2c;r3c;r4a;r5a;r6a;r7a;r4c;r5c;r6c;r7c];
  return rp;
}

proc __ntt_level1(rp : coeff Array256.t) : coeff Array256.t = {

  var zeta1,zeta1k : coeff Array16.t; 
  var r0, r1, r2, r3, r4, r5, r6, r7 : coeff Array16.t;
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0k, r1k, r2k, r3k, r4k, r5k, r6k, r7k : coeff Array16.t;
  var r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l : coeff Array16.t;

  (r0,r1,r2,r3,r4,r5,r6,r7) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r0k,r1k,r2k,r3k,r4k,r5k,r6k,r7k) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);

  (* first 128 *)
  zeta1 <- Array16.init (fun i => incoeff 2580);

  (r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a) <@ 
       __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta1, zeta1);
       
  (* second 128 *)
       
  zeta1k <- Array16.init (fun i => incoeff 3289);

  (r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l) <@ 
      __butterfly64x(r0k, r1k, r2k, r3k, r4k, r5k, r6k, r7k, zeta1k, zeta1k);
    
  rp <- CS2P [r0a;r1a;r2a;r3a;r4a;r5a;r6a;r7a;r0l;r1l;r2l;r3l;r4l;r5l;r6l;r7l];
  return rp;
}

proc __ntt_level2(rp : coeff Array256.t) : coeff Array256.t = {

  var zeta1b, zeta1m : coeff Array16.t; 
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b : coeff Array16.t;
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;
  var r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l : coeff Array16.t;
  var r0m, r1m, r2m, r3m, r4m, r5m, r6m, r7m : coeff Array16.t;
  var r0n, r1n, r2n, r3n, r4n, r5n, r6n, r7n : coeff Array16.t;

  (r0a,r1a,r2a,r3a,r4a,r5a,r6a,r7a) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r0l,r1l,r2l,r3l,r4l,r5l,r6l,r7l) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);

  zeta1b <- Array16.of_list witness
             [ incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642;
               incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630 ];

  (r0b,r4b) <- shuffle8 r0a r4a;
  (r1b,r5b) <- shuffle8 r1a r5a;
  (r2b,r6b) <- shuffle8 r2a r6a;
  (r3b,r7b) <- shuffle8 r3a r7a;

  (r0c, r4c, r1c, r5c, r2c, r6c, r3c, r7c) <@ 
      __butterfly64x(r0b, r4b, r1b, r5b, r2b, r6b, r3b, r7b, zeta1b, zeta1b);
  
  zeta1m <- Array16.of_list witness
             [ incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; 
               incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848 ];

  (r0m,r4m) <- shuffle8 r0l r4l;
  (r1m,r5m) <- shuffle8 r1l r5l;
  (r2m,r6m) <- shuffle8 r2l r6l;
  (r3m,r7m) <- shuffle8 r3l r7l;

  (r0n, r4n, r1n, r5n, r2n, r6n, r3n, r7n) <@ 
      __butterfly64x(r0m, r4m, r1m, r5m, r2m, r6m, r3m, r7m, zeta1m, zeta1m);
      
  return CS2P [r0c;r4c;r1c;r5c;r2c;r6c;r3c;r7c;r0n;r4n;r1n;r5n;r2n;r6n;r3n;r7n];

}
  
proc __ntt_level3(rp : coeff Array256.t) : coeff Array256.t = {
  var zeta1d, zeta1o : coeff Array16.t; 
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;
  var r0d, r1d, r2d, r3d, r4d, r5d, r6d, r7d : coeff Array16.t;
  var r0e, r1e, r2e, r3e, r4e, r5e, r6e, r7e : coeff Array16.t;
  var r0n, r1n, r2n, r3n, r4n, r5n, r6n, r7n : coeff Array16.t;
  var r0o, r1o, r2o, r3o, r4o, r5o, r6o, r7o : coeff Array16.t;
  var r0p, r1p, r2p, r3p, r4p, r5p, r6p, r7p : coeff Array16.t;
  var r1_,r2_,r3_,r4_,r5_,r6_,r7_,r8_,r9_,r10_,r11_,r12_,r13_,r14_,r15_,r16_ : coeff Array16.t;

  (r0c, r4c, r1c, r5c, r2c, r6c, r3c, r7c) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r0n, r4n, r1n, r5n, r2n, r6n, r3n, r7n) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);
  
  zeta1d <- Array16.of_list witness
             [ incoeff 1062; incoeff 1062; incoeff 1062; incoeff 1062; 
               incoeff 1919; incoeff 1919; incoeff 1919; incoeff 1919; 
               incoeff 193; incoeff 193; incoeff 193; incoeff 193; 
               incoeff 797; incoeff 797; incoeff 797; incoeff 797 ];

  (r0d,r2d) <- shuffle4 r0c r2c;
  (r4d,r6d) <- shuffle4 r4c r6c;
  (r1d,r3d) <- shuffle4 r1c r3c;
  (r5d,r7d) <- shuffle4 r5c r7c;

  (r0e, r2e, r4e, r6e, r1e, r3e, r5e, r7e) <@ 
       __butterfly64x(r0d, r2d, r4d, r6d, r1d, r3d, r5d, r7d, zeta1d, zeta1d);

  zeta1o <- Array16.of_list witness
             [ incoeff 2786; incoeff 2786; incoeff 2786; incoeff 2786; 
               incoeff 3260; incoeff 3260; incoeff 3260; incoeff 3260; 
               incoeff 569; incoeff 569; incoeff 569; incoeff 569; 
               incoeff 1746; incoeff 1746; incoeff 1746; incoeff 1746 ];

  (r0o,r2o) <- shuffle4 r0n r2n;
  (r4o,r6o) <- shuffle4 r4n r6n;
  (r1o,r3o) <- shuffle4 r1n r3n;
  (r5o,r7o) <- shuffle4 r5n r7n;
  
  (r0p, r2p, r4p, r6p, r1p, r3p, r5p, r7p) <@ 
       __butterfly64x(r0o, r2o, r4o, r6o, r1o, r3o, r5o, r7o, zeta1o, zeta1o);

  return CS2P [r0e;r2e;r4e;r6e;r1e;r3e;r5e;r7e;r0p;r2p;r4p;r6p;r1p;r3p;r5p;r7p];      
}

proc __ntt_level4(rp : coeff Array256.t) : coeff Array256.t = {

  var zeta1f, zeta1q : coeff Array16.t; 
  var r0e, r1e, r2e, r3e, r4e, r5e, r6e, r7e : coeff Array16.t;
  var r0f, r1f, r2f, r3f, r4f, r5f, r6f, r7f : coeff Array16.t;
  var r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g : coeff Array16.t;
  var r0p, r1p, r2p, r3p, r4p, r5p, r6p, r7p : coeff Array16.t;
  var r0q, r1q, r2q, r3q, r4q, r5q, r6q, r7q : coeff Array16.t;
  var r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r : coeff Array16.t;
  var rp1, rp2, rp3, rp4, rp5, rp6, rp7, rp8 : coeff Array256.t;

  (r0e,r2e,r4e,r6e,r1e,r3e,r5e,r7e) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r0p,r2p,r4p,r6p,r1p,r3p,r5p,r7p) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);
  
  zeta1f <- Array16.of_list witness
             [ incoeff 296; incoeff 296; incoeff 2447; incoeff 2447; 
               incoeff 1339; incoeff 1339; incoeff 1476; incoeff 1476; 
               incoeff 3046; incoeff 3046; incoeff 56; incoeff 56; 
               incoeff 2240; incoeff 2240; incoeff 1333; incoeff 1333 ];

  (r0f, r1f) <- shuffle2 r0e r1e;
  (r2f, r3f) <- shuffle2 r2e r3e;
  (r4f, r5f) <- shuffle2 r4e r5e;
  (r6f, r7f) <- shuffle2 r6e r7e;

  (r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g) <@ 
         __butterfly64x(r0f, r1f, r2f, r3f, r4f, r5f, r6f, r7f, zeta1f, zeta1f);
  
  zeta1q <- Array16.of_list witness
             [ incoeff 1426; incoeff 1426; incoeff 2094; incoeff 2094; 
               incoeff 535; incoeff 535; incoeff 2882; incoeff 2882; 
               incoeff 2393; incoeff 2393; incoeff 2879; incoeff 2879; 
               incoeff 1974; incoeff 1974; incoeff 821; incoeff 821 ];

  (r0q, r1q) <- shuffle2 r0p r1p;
  (r2q, r3q) <- shuffle2 r2p r3p;
  (r4q, r5q) <- shuffle2 r4p r5p;
  (r6q, r7q) <- shuffle2 r6p r7p;

  (r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r) <@ 
         __butterfly64x(r0q, r1q, r2q, r3q, r4q, r5q, r6q, r7q, zeta1q, zeta1q);

  return CS2P [r0g;r1g;r2g;r3g;r4g;r5g;r6g;r7g;r0r;r1r;r2r;r3r;r4r;r5r;r6r;r7r];

}

proc __ntt_level5(rp : coeff Array256.t) : coeff Array256.t = {

  var zeta1h, zeta1s : coeff Array16.t; 
  
  var r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g : coeff Array16.t;
  var r0h, r1h, r2h, r3h, r4h, r5h, r6h, r7h : coeff Array16.t;
  var r0i, r1i, r2i, r3i, r4i, r5i, r6i, r7i : coeff Array16.t;
  var r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r : coeff Array16.t;
  var r0s, r1s, r2s, r3s, r4s, r5s, r6s, r7s : coeff Array16.t;
  var r0t, r1t, r2t, r3t, r4t, r5t, r6t, r7t : coeff Array16.t;
  var rp1, rp2, rp3, rp4, rp5, rp6, rp7, rp8 : coeff Array256.t;

  (r0g,r1g,r2g,r3g,r4g,r5g,r6g,r7g) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r0r,r1r,r2r,r3r,r4r,r5r,r6r,r7r) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);
 
  zeta1h <- Array16.of_list witness
             [ incoeff 289; incoeff 331; incoeff 3253; incoeff 1756; incoeff 1197; incoeff 2304; incoeff 2277; incoeff 2055; incoeff 650; incoeff 1977; incoeff 2513; incoeff 632; incoeff 2865; incoeff 33; incoeff 1320; incoeff 1915 ];

  (r0h,r4h) <- shuffle1 r0g r4g;
  (r1h,r5h) <- shuffle1 r1g r5g;
  (r2h,r6h) <- shuffle1 r2g r6g;
  (r3h,r7h) <- shuffle1 r3g r7g;

  ( r0i, r4i, r1i, r5i, r2i, r6i, r3i, r7i ) <@ 
       __butterfly64x(r0h, r4h, r1h, r5h, r2h, r6h, r3h, r7h, zeta1h, zeta1h);
  
  zeta1s <- Array16.of_list witness
             [ incoeff 2319; incoeff 1435; incoeff 807; incoeff 452; incoeff 1438; incoeff 2868; incoeff 1534; incoeff 2402; incoeff 2647; incoeff 2617; incoeff 1481; incoeff 648; incoeff 2474; incoeff 3110; incoeff 1227; incoeff 910 ];

  (r0s,r4s) <- shuffle1 r0r r4r;
  (r1s,r5s) <- shuffle1 r1r r5r;
  (r2s,r6s) <- shuffle1 r2r r6r;
  (r3s,r7s) <- shuffle1 r3r r7r;

  ( r0t, r4t, r1t, r5t, r2t, r6t, r3t, r7t ) <@ 
       __butterfly64x(r0s, r4s, r1s, r5s, r2s, r6s, r3s, r7s, zeta1s, zeta1s);
  
  return CS2P [r0i;r4i;r1i;r5i;r2i;r6i;r3i;r7i;r0t;r4t;r1t;r5t;r2t;r6t;r3t;r7t];
}
  
proc __ntt_level6(rp : coeff Array256.t) : coeff Array256.t = {

  var zeta2i, zeta3i, zeta2t, zeta3t : coeff Array16.t; 
  var r0i, r1i, r2i, r3i, r4i, r5i, r6i, r7i : coeff Array16.t;
  var r0j, r1j, r2j, r3j, r4j, r5j, r6j, r7j : coeff Array16.t;
  var r0t, r1t, r2t, r3t, r4t, r5t, r6t, r7t : coeff Array16.t;
  var r0u, r1u, r2u, r3u, r4u, r5u, r6u, r7u : coeff Array16.t;
  
  (r0i,r4i,r1i,r5i,r2i,r6i,r3i,r7i) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r0t,r4t,r1t,r5t,r2t,r6t,r3t,r7t) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);
  
  zeta2i <- Array16.of_list witness
             [ incoeff 17; incoeff 583; incoeff 1637; incoeff 2288; incoeff 1409; incoeff 3281; incoeff 756; incoeff 3015; 
               incoeff 1703; incoeff 2789; incoeff 1847; incoeff 1461; incoeff 939; incoeff 2437; incoeff 733; incoeff 268 ];
  zeta3i <- Array16.of_list witness
             [ incoeff 2761; incoeff 2649; incoeff 723; incoeff 1100; incoeff 2662; incoeff 233; incoeff 2156; incoeff 3050; 
               incoeff 1651; incoeff 1789; incoeff 952; incoeff 2687; incoeff 2308; incoeff 2388; incoeff 2337; incoeff 641 ];
           
  (r0j, r4j, r2j, r6j, r1j, r5j, r3j, r7j) <@ 
        __butterfly64x(r0i, r4i, r2i, r6i, r1i, r5i, r3i, r7i, zeta2i, zeta3i);

  zeta2t <- Array16.of_list witness
             [ incoeff 1584; incoeff 2037; incoeff 375; incoeff 2090; incoeff 1063; incoeff 2773; incoeff 2099; incoeff 2466;
               incoeff 2804; incoeff 403; incoeff 1143; incoeff 2775; incoeff 1722; incoeff 1874; incoeff 2110; incoeff 885 ];
  zeta3t <- Array16.of_list witness
             [ incoeff 2298; incoeff 3220; incoeff 2549; incoeff 1645; incoeff 319; incoeff 757; incoeff 561; incoeff 2594;
               incoeff 1092; incoeff 1026; incoeff 2150; incoeff 886; incoeff 1212; incoeff 1029; incoeff 2935; incoeff 2154 ];

  (r0u, r4u, r2u, r6u, r1u, r5u, r3u, r7u) <@ 
        __butterfly64x(r0t, r4t, r2t, r6t, r1t, r5t, r3t, r7t, zeta2t, zeta3t);
  
  return CS2P [r0j;r4j;r1j;r5j;r2j;r6j;r3j;r7j;r0u;r4u;r1u;r5u;r2u;r6u;r3u;r7u];
}
 proc ntt(rp : coeff Array256.t) : coeff Array256.t = {
  var zeta1, zeta1b, zeta1d : coeff Array16.t; 
  var zeta1f, zeta1h, zeta2i, zeta3i : coeff Array16.t; 
  var zeta1k, zeta1m, zeta1o : coeff Array16.t; 
  var zeta1q, zeta1s, zeta2t, zeta3t : coeff Array16.t; 
  var r0, r1, r2, r3, r4, r5, r6, r7 : coeff Array16.t;
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b : coeff Array16.t;
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;
  var r0d, r1d, r2d, r3d, r4d, r5d, r6d, r7d : coeff Array16.t;
  var r0e, r1e, r2e, r3e, r4e, r5e, r6e, r7e : coeff Array16.t;
  var r0f, r1f, r2f, r3f, r4f, r5f, r6f, r7f : coeff Array16.t;
  var r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g : coeff Array16.t;
  var r0h, r1h, r2h, r3h, r4h, r5h, r6h, r7h : coeff Array16.t;
  var r0i, r1i, r2i, r3i, r4i, r5i, r6i, r7i : coeff Array16.t;
  var r0j, r1j, r2j, r3j, r4j, r5j, r6j, r7j : coeff Array16.t;
  var r0k, r1k, r2k, r3k, r4k, r5k, r6k, r7k : coeff Array16.t;
  var r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l : coeff Array16.t;
  var r0m, r1m, r2m, r3m, r4m, r5m, r6m, r7m : coeff Array16.t;
  var r0n, r1n, r2n, r3n, r4n, r5n, r6n, r7n : coeff Array16.t;
  var r0o, r1o, r2o, r3o, r4o, r5o, r6o, r7o : coeff Array16.t;
  var r0p, r1p, r2p, r3p, r4p, r5p, r6p, r7p : coeff Array16.t;
  var r0q, r1q, r2q, r3q, r4q, r5q, r6q, r7q : coeff Array16.t;
  var r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r : coeff Array16.t;
  var r0s, r1s, r2s, r3s, r4s, r5s, r6s, r7s : coeff Array16.t;
  var r0t, r1t, r2t, r3t, r4t, r5t, r6t, r7t : coeff Array16.t;
  var r0u, r1u, r2u, r3u, r4u, r5u, r6u, r7u : coeff Array16.t;
  var r0x, r1x, r2x, r3x, r4x, r5x, r6x, r7x : coeff Array16.t;
  var rp1, rp2, rp3, rp4, rp5, rp6, rp7, rp8 : coeff Array256.t;
  var rp9, rp10, rp11, rp12, rp13, rp14, rp15, rp16 : coeff Array256.t;

  (r0,r1,r2,r3,r0b,r1b,r2b,r3b) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r4,r5,r6,r7,r4b,r5b,r6b,r7b) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);

  zeta1 <- Array16.init (fun i => incoeff 1729);

  (r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a) <@ 
      __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta1, zeta1);

  (r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c) <@ 
      __butterfly64x(r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b, zeta1, zeta1);
      
  rp <- CS2P [r0a;r1a;r2a;r3a;r0c;r1c;r2c;r3c;r4a;r5a;r6a;r7a;r4c;r5c;r6c;r7c];

(**** LEFT-HALF*****)

  (* level 1 *)

   zeta1 <- Array16.init (fun i => incoeff 2580);

    r0 <- P2C rp 0;
    r1 <- P2C rp 1;
    r2 <- P2C rp 2;
    r3 <- P2C rp 3;
    r4 <- P2C rp 4;
    r5 <- P2C rp 5;
    r6 <- P2C rp 6;
    r7 <- P2C rp 7;

    (r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a) <@ 
        __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta1, zeta1);

    (* level 2 *)

  zeta1b <- Array16.of_list witness
             [ incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642; incoeff 2642;
               incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630; incoeff 630 ];


    (r0b,r4b) <- shuffle8 r0a r4a;
    (r1b,r5b) <- shuffle8 r1a r5a;
    (r2b,r6b) <- shuffle8 r2a r6a;
    (r3b,r7b) <- shuffle8 r3a r7a;

    (r0c, r4c, r1c, r5c, r2c, r6c, r3c, r7c) <@ 
        __butterfly64x(r0b, r4b, r1b, r5b, r2b, r6b, r3b, r7b, zeta1b, zeta1b);
    
    (* level 3 *)

  zeta1d <- Array16.of_list witness
             [ incoeff 1062; incoeff 1062; incoeff 1062; incoeff 1062; 
               incoeff 1919; incoeff 1919; incoeff 1919; incoeff 1919; 
               incoeff 193; incoeff 193; incoeff 193; incoeff 193; 
               incoeff 797; incoeff 797; incoeff 797; incoeff 797 ];

    (r0d,r2d) <- shuffle4 r0c r2c;
    (r4d,r6d) <- shuffle4 r4c r6c;
    (r1d,r3d) <- shuffle4 r1c r3c;
    (r5d,r7d) <- shuffle4 r5c r7c;

    (r0e, r2e, r4e, r6e, r1e, r3e, r5e, r7e) <@ 
         __butterfly64x(r0d, r2d, r4d, r6d, r1d, r3d, r5d, r7d, zeta1d, zeta1d);

    (* level 4 *)

  zeta1f <- Array16.of_list witness
             [ incoeff 296; incoeff 296; incoeff 2447; incoeff 2447; 
               incoeff 1339; incoeff 1339; incoeff 1476; incoeff 1476; 
               incoeff 3046; incoeff 3046; incoeff 56; incoeff 56; 
               incoeff 2240; incoeff 2240; incoeff 1333; incoeff 1333 ];


    (r0f, r1f) <- shuffle2 r0e r1e;
    (r2f, r3f) <- shuffle2 r2e r3e;
    (r4f, r5f) <- shuffle2 r4e r5e;
    (r6f, r7f) <- shuffle2 r6e r7e;

    (r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g) <@ 
           __butterfly64x(r0f, r1f, r2f, r3f, r4f, r5f, r6f, r7f, zeta1f, zeta1f);

    (* level 5 *)

  zeta1h <- Array16.of_list witness
             [ incoeff 289; incoeff 331; incoeff 3253; incoeff 1756; incoeff 1197; incoeff 2304; incoeff 2277; incoeff 2055; incoeff 650; incoeff 1977; incoeff 2513; incoeff 632; incoeff 2865; incoeff 33; incoeff 1320; incoeff 1915 ];


    (r0h,r4h) <- shuffle1 r0g r4g;
    (r1h,r5h) <- shuffle1 r1g r5g;
    (r2h,r6h) <- shuffle1 r2g r6g;
    (r3h,r7h) <- shuffle1 r3g r7g;

    ( r0i, r4i, r1i, r5i, r2i, r6i, r3i, r7i ) <@ 
         __butterfly64x(r0h, r4h, r1h, r5h, r2h, r6h, r3h, r7h, zeta1h, zeta1h);

    (* level 6 *)

  zeta2i <- Array16.of_list witness
             [ incoeff 17; incoeff 583; incoeff 1637; incoeff 2288; incoeff 1409; incoeff 3281; incoeff 756; incoeff 3015; 
               incoeff 1703; incoeff 2789; incoeff 1847; incoeff 1461; incoeff 939; incoeff 2437; incoeff 733; incoeff 268 ];
  zeta3i <- Array16.of_list witness
             [ incoeff 2761; incoeff 2649; incoeff 723; incoeff 1100; incoeff 2662; incoeff 233; incoeff 2156; incoeff 3050; 
               incoeff 1651; incoeff 1789; incoeff 952; incoeff 2687; incoeff 2308; incoeff 2388; incoeff 2337; incoeff 641 ];


    (r0j, r4j, r2j, r6j, r1j, r5j, r3j, r7j) <@ 
          __butterfly64x(r0i, r4i, r2i, r6i, r1i, r5i, r3i, r7i, zeta2i, zeta3i);

    
    rp1 <- PUC rp 0 r0j;
    rp2 <- PUC rp1 1 r4j;
    rp3 <- PUC rp2 2 r1j;
    rp4 <- PUC rp3 3 r5j;
    rp5 <- PUC rp4 4 r2j;
    rp6 <- PUC rp5 5 r6j;
    rp7 <- PUC rp6 6 r3j;
    rp8 <- PUC rp7 7 r7j;

(**** RIGHT-HALF*****)

  (* level 1 *)

  zeta1k <- Array16.init (fun i => incoeff 3289);

    r0k <- P2C rp 8;
    r1k <- P2C rp 9;
    r2k <- P2C rp 10;
    r3k <- P2C rp 11;
    r4k <- P2C rp 12;
    r5k <- P2C rp 13;
    r6k <- P2C rp 14;
    r7k <- P2C rp 15;

    (r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l) <@ 
        __butterfly64x(r0k, r1k, r2k, r3k, r4k, r5k, r6k, r7k, zeta1k, zeta1k);

    (* level 2 *)

  zeta1m <- Array16.of_list witness
             [ incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; incoeff 1897; 
               incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848; incoeff 848 ];

    (r0m,r4m) <- shuffle8 r0l r4l;
    (r1m,r5m) <- shuffle8 r1l r5l;
    (r2m,r6m) <- shuffle8 r2l r6l;
    (r3m,r7m) <- shuffle8 r3l r7l;

    (r0n, r4n, r1n, r5n, r2n, r6n, r3n, r7n) <@ 
        __butterfly64x(r0m, r4m, r1m, r5m, r2m, r6m, r3m, r7m, zeta1m, zeta1m);

    (* level 3 *)

  zeta1o <- Array16.of_list witness
             [ incoeff 2786; incoeff 2786; incoeff 2786; incoeff 2786; 
               incoeff 3260; incoeff 3260; incoeff 3260; incoeff 3260; 
               incoeff 569; incoeff 569; incoeff 569; incoeff 569; 
               incoeff 1746; incoeff 1746; incoeff 1746; incoeff 1746 ];


    (r0o,r2o) <- shuffle4 r0n r2n;
    (r4o,r6o) <- shuffle4 r4n r6n;
    (r1o,r3o) <- shuffle4 r1n r3n;
    (r5o,r7o) <- shuffle4 r5n r7n;

    (r0p, r2p, r4p, r6p, r1p, r3p, r5p, r7p) <@ 
         __butterfly64x(r0o, r2o, r4o, r6o, r1o, r3o, r5o, r7o, zeta1o, zeta1o);

    (* level 4 *)

  zeta1q <- Array16.of_list witness
             [ incoeff 1426; incoeff 1426; incoeff 2094; incoeff 2094; 
               incoeff 535; incoeff 535; incoeff 2882; incoeff 2882; 
               incoeff 2393; incoeff 2393; incoeff 2879; incoeff 2879; 
               incoeff 1974; incoeff 1974; incoeff 821; incoeff 821 ];

    (r0q, r1q) <- shuffle2 r0p r1p;
    (r2q, r3q) <- shuffle2 r2p r3p;
    (r4q, r5q) <- shuffle2 r4p r5p;
    (r6q, r7q) <- shuffle2 r6p r7p;

    (r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r) <@ 
           __butterfly64x(r0q, r1q, r2q, r3q, r4q, r5q, r6q, r7q, zeta1q, zeta1q);

    (* level 5 *)

  zeta1s <- Array16.of_list witness
             [ incoeff 2319; incoeff 1435; incoeff 807; incoeff 452; incoeff 1438; incoeff 2868; incoeff 1534; incoeff 2402; incoeff 2647; incoeff 2617; incoeff 1481; incoeff 648; incoeff 2474; incoeff 3110; incoeff 1227; incoeff 910 ];

    (r0s,r4s) <- shuffle1 r0r r4r;
    (r1s,r5s) <- shuffle1 r1r r5r;
    (r2s,r6s) <- shuffle1 r2r r6r;
    (r3s,r7s) <- shuffle1 r3r r7r;

    ( r0t, r4t, r1t, r5t, r2t, r6t, r3t, r7t ) <@ 
         __butterfly64x(r0s, r4s, r1s, r5s, r2s, r6s, r3s, r7s, zeta1s, zeta1s);

    (* level 6 *)

  zeta2t <- Array16.of_list witness
             [ incoeff 1584; incoeff 2037; incoeff 375; incoeff 2090; incoeff 1063; incoeff 2773; incoeff 2099; incoeff 2466;
               incoeff 2804; incoeff 403; incoeff 1143; incoeff 2775; incoeff 1722; incoeff 1874; incoeff 2110; incoeff 885 ];
  zeta3t <- Array16.of_list witness
             [ incoeff 2298; incoeff 3220; incoeff 2549; incoeff 1645; incoeff 319; incoeff 757; incoeff 561; incoeff 2594;
               incoeff 1092; incoeff 1026; incoeff 2150; incoeff 886; incoeff 1212; incoeff 1029; incoeff 2935; incoeff 2154 ];

    (r0u, r4u, r2u, r6u, r1u, r5u, r3u, r7u) <@ 
          __butterfly64x(r0t, r4t, r2t, r6t, r1t, r5t, r3t, r7t, zeta2t, zeta3t);

    rp9  <- PUC rp8 8 r0u;
    rp10 <-  PUC rp9 9 r4u;
    rp11 <-  PUC rp10 10 r1u;
    rp12 <- PUC rp11 11 r5u;
    rp13 <- PUC rp12 12 r2u;
    rp14 <- PUC rp13 13 r6u;
    rp15 <- PUC rp14 14 r3u;
    rp16 <- PUC rp15 15 r7u;

    return rp16;
 }

 proc ntt0t6(r : coeff Array256.t) : coeff Array256.t = {
  var rp0,rp1,rp2,rp3,rp4,rp5,rp6;
  rp0 <@ __ntt_level0(r);
  rp1 <@ __ntt_level1(rp0);
  rp2 <@ __ntt_level2(rp1);
  rp3 <@ __ntt_level3(rp2);
  rp4 <@ __ntt_level4(rp3);
  rp5 <@ __ntt_level5(rp4);
  rp6 <@ __ntt_level6(rp5);
  return rp6;
 }

 proc ntt_bsrev(r : coeff Array256.t) : coeff Array256.t = {
  NTT_vars.r <- r;
  NTT_vars.zetas <- NTT_Fq.zetas;
  r <@ NTT_bsrev.ntt();
  return r;
 }

proc __invntt___butterfly64x(rl0t rl1t rl2t rl3t rh0t rh1t rh2t rh3t z0 z1: coeff Array16.t) : coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t * coeff Array16.t = {

  var rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3;

  rh0 <- Array16.init (fun i => z0.[i] * (rl0t.[i] - rh0t.[i]));
  rl0 <- Array16.init (fun i => rl0t.[i] + rh0t.[i]);
  
  rh1 <- Array16.init (fun i => z0.[i] * (rl1t.[i] - rh1t.[i]));
  rl1 <- Array16.init (fun i => rl1t.[i] + rh1t.[i]);
  
  rh2 <- Array16.init (fun i => z1.[i] * (rl2t.[i] - rh2t.[i]));
  rl2 <- Array16.init (fun i => rl2t.[i] + rh2t.[i]);
  
  rh3 <- Array16.init (fun i => z1.[i] * (rl3t.[i] - rh3t.[i]));
  rl3 <- Array16.init (fun i => rl3t.[i] + rh3t.[i]);
  
  return (rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3);
}

proc __invntt_level0(rp : coeff Array256.t) : coeff Array256.t =
{
  var zeta0, zeta1, zeta0k, zeta1k : coeff Array16.t;
  var r0, r1, r2, r3, r4, r5, r6, r7 : coeff Array16.t;
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0k, r1k, r2k, r3k, r4k, r5k, r6k, r7k : coeff Array16.t;
  var r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l : coeff Array16.t;

  zeta0 <- Array16.of_list witness [incoeff 1175 ; incoeff 394 ; incoeff 2300 ; incoeff 2117 ; incoeff 2443 ; incoeff 1179 ; incoeff 2303 ; incoeff 2237 ; incoeff 735 ; incoeff 2768 ; incoeff 2572 ; incoeff 3010; incoeff 1684 ; incoeff 780 ; incoeff 109 ; incoeff 1031];
  zeta1 <- Array16.of_list witness [incoeff 2444 ; incoeff 1219 ; incoeff 1455 ; incoeff 1607 ; incoeff 554 ; incoeff 2186 ; incoeff 2926 ; incoeff 525 ; incoeff 863 ; incoeff 1230 ; incoeff 556 ; incoeff 2266 ; incoeff 1239 ; incoeff 2954 ; incoeff 1292 ; incoeff 1745];
  
  (r0,r1,r2,r3,r4,r5,r6,r7) <- (P2C rp 0,P2C rp 1,P2C rp 2,P2C rp 3,P2C rp 4,P2C rp 5,P2C rp 6,P2C rp 7);

  (r0a, r1a, r4a, r5a, r2a, r3a, r6a, r7a) <@ __invntt___butterfly64x(r0, r1, r4, r5, r2, r3, r6, r7, zeta0, zeta1);
  
  zeta0k <- Array16.of_list witness [incoeff 2688 ; incoeff 992; incoeff 941; incoeff 1021; incoeff 642; incoeff 2377; incoeff 1540; incoeff 1678; incoeff 279; incoeff 1173; incoeff 3096; incoeff 667; incoeff 2229; incoeff 2606; incoeff 680; incoeff 568 ];
  zeta1k <- Array16.of_list witness [incoeff 3061 ; incoeff 2596 ; incoeff 892 ; incoeff 2390 ; incoeff 1868 ; incoeff 1482 ; incoeff 540 ; incoeff 1626; incoeff 314 ; incoeff 2573 ; incoeff 48 ; incoeff 1920 ; incoeff 1041 ; incoeff 1692 ; incoeff 2746 ; incoeff 3312 ];

  (r0k,r1k,r2k,r3k,r4k,r5k,r6k,r7k) <- (P2C rp 8,P2C rp 9,P2C rp 10,P2C rp 11,P2C rp 12,P2C rp 13,P2C rp 14,P2C rp 15);

  (r0l, r1l, r4l, r5l, r2l, r3l, r6l, r7l) <@ __invntt___butterfly64x(r0k, r1k, r4k, r5k, r2k, r3k, r6k, r7k, zeta0k, zeta1k);
  
  return CS2P [r0a;r1a;r4a;r5a;r2a;r3a;r6a;r7a;r0l;r1l;r4l;r5l;r2l;r3l;r6l;r7l];
}

proc __invntt_level1(rp : coeff Array256.t) : coeff Array256.t =
{
  var zeta1a, zeta1l : coeff Array16.t;
  var r0, r1, r2, r3, r4, r5, r6, r7 : coeff Array16.t;
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b : coeff Array16.t;
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;
  var r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l : coeff Array16.t;
  var r0m, r1m, r2m, r3m, r4m, r5m, r6m, r7m : coeff Array16.t;
  var r0n, r1n, r2n, r3n, r4n, r5n, r6n, r7n : coeff Array16.t;
  
  zeta1a <- Array16.of_list witness [ incoeff 2419 ; incoeff 2102 ; incoeff 219 ; incoeff 855 ; incoeff 2681 ; incoeff 1848 ; incoeff 712 ; incoeff 682 ; incoeff 927 ; incoeff 1795 ; incoeff 461 ; incoeff 1891 ; incoeff 2877 ; incoeff 2522 ; incoeff 1894 ; incoeff 1010 ];
  
  (r0a,r1a,r4a,r5a,r2a,r3a,r6a,r7a) <- (P2C rp 0,P2C rp 1,P2C rp 2,P2C rp 3,P2C rp 4,P2C rp 5,P2C rp 6,P2C rp 7);
  (r0l,r1l,r4l,r5l,r2l,r3l,r6l,r7l) <- (P2C rp 8,P2C rp 9,P2C rp 10,P2C rp 11,P2C rp 12,P2C rp 13,P2C rp 14,P2C rp 15);

  (r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b) <@ __invntt___butterfly64x(r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a, zeta1a, zeta1a);
  
  (r0c,r1c) <- shuffle1 r0b r1b;
  (r2c,r3c) <- shuffle1 r2b r3b;
  (r4c,r5c) <- shuffle1 r4b r5b;
  (r6c,r7c) <- shuffle1 r6b r7b;
  
  zeta1l <- Array16.of_list witness
             [ incoeff 1414 ; incoeff 2009 ; incoeff 3296 ; incoeff 464 ; incoeff 2697 ; incoeff 816 ; incoeff 1352 ; incoeff 2679 ; incoeff 1274 ; incoeff 1052 ; incoeff 1025 ; incoeff 2132 ; incoeff 1573 ; incoeff 76 ; incoeff 2998 ; incoeff 3040 ];

  (r0m, r1m, r2m, r3m, r4m, r5m, r6m, r7m) <@ __invntt___butterfly64x(r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l, zeta1l, zeta1l);

  (r0n,r1n) <- shuffle1 r0m r1m;
  (r2n,r3n) <- shuffle1 r2m r3m;
  (r4n,r5n) <- shuffle1 r4m r5m;
  (r6n,r7n) <- shuffle1 r6m r7m;
  
  return CS2P [r0c;r1c;r2c;r3c;r4c;r5c;r6c;r7c;r0n;r1n;r2n;r3n;r4n;r5n;r6n;r7n];
}

proc __invntt_level2(rp : coeff Array256.t) : coeff Array256.t =
{
  var zeta1c, zeta1n : coeff Array16.t;
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;
  var r0d, r1d, r2d, r3d, r4d, r5d, r6d, r7d : coeff Array16.t;
  var r0e, r1e, r2e, r3e, r4e, r5e, r6e, r7e : coeff Array16.t;
  var r0n, r1n, r2n, r3n, r4n, r5n, r6n, r7n : coeff Array16.t;
  var r0o, r1o, r2o, r3o, r4o, r5o, r6o, r7o : coeff Array16.t;
  var r0p, r1p, r2p, r3p, r4p, r5p, r6p, r7p : coeff Array16.t;
  
  zeta1c <- Array16.of_list witness [ incoeff 2508 ; incoeff 2508; incoeff 1355 ; incoeff 1355; incoeff 450 ; incoeff 450; incoeff 936; incoeff 936 ; incoeff 447; incoeff 447 ; incoeff 2794; incoeff 2794 ; incoeff 1235; incoeff 1235 ; incoeff 1903; incoeff 1903 ];
  
  (r0c,r1c,r2c,r3c,r4c,r5c,r6c,r7c) <- (P2C rp 0,P2C rp 1,P2C rp 2,P2C rp 3,P2C rp 4,P2C rp 5,P2C rp 6,P2C rp 7);
  (r0n,r1n,r2n,r3n,r4n,r5n,r6n,r7n) <- (P2C rp 8,P2C rp 9,P2C rp 10,P2C rp 11,P2C rp 12,P2C rp 13,P2C rp 14,P2C rp 15);

  (r0d, r2d, r4d, r6d, r1d, r3d, r5d, r7d) <@ __invntt___butterfly64x(r0c, r2c, r4c, r6c, r1c, r3c, r5c, r7c, zeta1c, zeta1c);

  (r0e,r2e) <- shuffle2 r0d r2d;
  (r4e,r6e) <- shuffle2 r4d r6d;
  (r1e,r3e) <- shuffle2 r1d r3d;
  (r5e,r7e) <- shuffle2 r5d r7d;
  
  zeta1n <- Array16.of_list witness
             [ incoeff 1996 ; incoeff 1996; incoeff 1089 ; incoeff 1089; incoeff 3273 ; incoeff 3273; incoeff 283 ; incoeff 283; incoeff 1853 ; incoeff 1853; incoeff 1990 ; incoeff 1990; incoeff 882 ; incoeff 882; incoeff 3033; incoeff 3033 ];

  (r0o, r2o, r4o, r6o, r1o, r3o, r5o, r7o) <@ __invntt___butterfly64x(r0n, r2n, r4n, r6n, r1n, r3n, r5n, r7n, zeta1n, zeta1n);

  (r0p,r2p) <- shuffle2 r0o r2o;
  (r4p,r6p) <- shuffle2 r4o r6o;
  (r1p,r3p) <- shuffle2 r1o r3o;
  (r5p,r7p) <- shuffle2 r5o r7o;
  
  return CS2P [r0e;r2e;r4e;r6e;r1e;r3e;r5e;r7e;r0p;r2p;r4p;r6p;r1p;r3p;r5p;r7p];
}

proc __invntt_level3(rp : coeff Array256.t) : coeff Array256.t =
{ 
  var zeta1e, zeta1p : coeff Array16.t;
  var r0e, r1e, r2e, r3e, r4e, r5e, r6e, r7e : coeff Array16.t;
  var r0f, r1f, r2f, r3f, r4f, r5f, r6f, r7f : coeff Array16.t;
  var r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g : coeff Array16.t;
  var r0p, r1p, r2p, r3p, r4p, r5p, r6p, r7p : coeff Array16.t;
  var r0q, r1q, r2q, r3q, r4q, r5q, r6q, r7q : coeff Array16.t;  
  var r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r : coeff Array16.t;

  zeta1e <- Array16.of_list witness [ incoeff 1583; incoeff 1583; incoeff 1583; incoeff 1583 ; incoeff 2760; incoeff 2760; incoeff 2760; incoeff 2760 ; incoeff 69 ; incoeff 69; incoeff 69; incoeff 69; incoeff 543; incoeff 543; incoeff 543; incoeff 543 ];
  
  (r0e,r2e,r4e,r6e,r1e,r3e,r5e,r7e) <- (P2C rp 0,P2C rp 1,P2C rp 2,P2C rp 3,P2C rp 4,P2C rp 5,P2C rp 6,P2C rp 7);
  (r0p,r2p,r4p,r6p,r1p,r3p,r5p,r7p) <- (P2C rp 8,P2C rp 9,P2C rp 10,P2C rp 11,P2C rp 12,P2C rp 13,P2C rp 14,P2C rp 15);

  (r0f, r4f, r1f, r5f, r2f, r6f, r3f, r7f) <@ __invntt___butterfly64x(r0e, r4e, r1e, r5e, r2e, r6e, r3e, r7e, zeta1e, zeta1e);

  (r0g,r4g) <- shuffle4 r0f r4f;
  (r1g,r5g) <- shuffle4 r1f r5f;
  (r2g,r6g) <- shuffle4 r2f r6f;
  (r3g,r7g) <- shuffle4 r3f r7f;
  
  zeta1p <- Array16.of_list witness
             [ incoeff 2532 ; incoeff 2532; incoeff 2532; incoeff 2532; incoeff 3136 ; incoeff 3136; incoeff 3136; incoeff 3136; incoeff 1410 ; incoeff 1410; incoeff 1410; incoeff 1410; incoeff 2267; incoeff 2267; incoeff 2267; incoeff 2267 ];

  (r0q, r4q, r1q, r5q, r2q, r6q, r3q, r7q) <@ __invntt___butterfly64x(r0p, r4p, r1p, r5p, r2p, r6p, r3p, r7p, zeta1p, zeta1p);

  (r0r,r4r) <- shuffle4 r0q r4q;
  (r1r,r5r) <- shuffle4 r1q r5q;
  (r2r,r6r) <- shuffle4 r2q r6q;
  (r3r,r7r) <- shuffle4 r3q r7q;
  
  return CS2P [r0g;r4g;r1g;r5g;r2g;r6g;r3g;r7g;r0r;r4r;r1r;r5r;r2r;r6r;r3r;r7r];
}

proc __invntt_level4(rp : coeff Array256.t) : coeff Array256.t =
{
  var zeta1g, zeta1r : coeff Array16.t;
  var r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g : coeff Array16.t;
  var r0h, r1h, r2h, r3h, r4h, r5h, r6h, r7h : coeff Array16.t;
  var r0i, r1i, r2i, r3i, r4i, r5i, r6i, r7i : coeff Array16.t;
  var r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r : coeff Array16.t;
  var r0s, r1s, r2s, r3s, r4s, r5s, r6s, r7s : coeff Array16.t;
  var r0t, r1t, r2t, r3t, r4t, r5t, r6t, r7t : coeff Array16.t;
  
  zeta1g <- Array16.of_list witness [ incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481; incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432 ];
  
  (r0g,r4g,r1g,r5g,r2g,r6g,r3g,r7g) <- (P2C rp 0,P2C rp 1,P2C rp 2,P2C rp 3,P2C rp 4,P2C rp 5,P2C rp 6,P2C rp 7);
  (r0r,r4r,r1r,r5r,r2r,r6r,r3r,r7r) <- (P2C rp 8,P2C rp 9,P2C rp 10,P2C rp 11,P2C rp 12,P2C rp 13,P2C rp 14,P2C rp 15);

  (r0h, r1h, r2h, r3h, r4h, r5h, r6h, r7h) <@ __invntt___butterfly64x(r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g, zeta1g, zeta1g);

  (r0i,r1i) <- shuffle8 r0h r1h;
  (r2i,r3i) <- shuffle8 r2h r3h;
  (r4i,r5i) <- shuffle8 r4h r5h;
  (r6i,r7i) <- shuffle8 r6h r7h;
  
  zeta1r <- Array16.of_list witness
             [ incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699 ; incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687 ];

  (r0s, r1s, r2s, r3s, r4s, r5s, r6s, r7s) <@ __invntt___butterfly64x(r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r, zeta1r, zeta1r);

  (r0t,r1t) <- shuffle8 r0s r1s;
  (r2t,r3t) <- shuffle8 r2s r3s;
  (r4t,r5t) <- shuffle8 r4s r5s;
  (r6t,r7t) <- shuffle8 r6s r7s;
  
  return CS2P [r0i;r1i;r2i;r3i;r4i;r5i;r6i;r7i;r0t;r1t;r2t;r3t;r4t;r5t;r6t;r7t];
}

proc __invntt_level5(rp : coeff Array256.t) : coeff Array256.t =
{
  var zeta1i, zeta1t : coeff Array16.t;
  var r0h, r1h, r2h, r3h, r4h, r5h, r6h, r7h : coeff Array16.t;
  var r0i, r1i, r2i, r3i, r4i, r5i, r6i, r7i : coeff Array16.t;
  var r0j, r1j, r2j, r3j, r4j, r5j, r6j, r7j : coeff Array16.t;
  var r0s, r1s, r2s, r3s, r4s, r5s, r6s, r7s : coeff Array16.t;
  var r0t, r1t, r2t, r3t, r4t, r5t, r6t, r7t : coeff Array16.t;
  var r0u, r1u, r2u, r3u, r4u, r5u, r6u, r7u : coeff Array16.t;

  zeta1i <- Array16.init (fun i => incoeff 40);
  
  (r0i,r1i,r2i,r3i,r4i,r5i,r6i,r7i) <- (P2C rp 0,P2C rp 1,P2C rp 2,P2C rp 3,P2C rp 4,P2C rp 5,P2C rp 6,P2C rp 7);
  (r0t,r1t,r2t,r3t,r4t,r5t,r6t,r7t) <- (P2C rp 8,P2C rp 9,P2C rp 10,P2C rp 11,P2C rp 12,P2C rp 13,P2C rp 14,P2C rp 15);

  (r0j, r2j, r4j, r6j, r1j, r3j, r5j, r7j) <@ __invntt___butterfly64x(r0i, r2i, r4i, r6i, r1i, r3i, r5i, r7i, zeta1i, zeta1i);
  
  zeta1t <- Array16.init (fun i => incoeff 749);

  (r0u, r2u, r4u, r6u, r1u, r3u, r5u, r7u) <@ __invntt___butterfly64x(r0t, r2t, r4t, r6t, r1t, r3t, r5t, r7t, zeta1t, zeta1t);
  
  return CS2P [r0j;r2j;r4j;r6j;r1j;r3j;r5j;r7j;r0u;r2u;r4u;r6u;r1u;r3u;r5u;r7u];
}

proc ___invntt_level6(rp : coeff Array256.t) : coeff Array256.t =
{
  var zeta0 : coeff Array16.t;
  var r0, r1, r2, r3, r4, r5, r6, r7 : coeff Array16.t;
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b : coeff Array16.t;
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;

  zeta0 <- Array16.init (fun i => incoeff 1600);
  
  (r0,r1,r2,r3,r0b,r1b,r2b,r3b) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
  (r4,r5,r6,r7,r4b,r5b,r6b,r7b) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);

  (r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a) <@ __invntt___butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta0, zeta0);

  (r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c) <@ __invntt___butterfly64x(r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b, zeta0, zeta0);

  return CS2P [r0a;r1a;r2a;r3a;r0c;r1c;r2c;r3c;r4a;r5a;r6a;r7a;r4c;r5c;r6c;r7c];
}

proc __invntt_level6(rp : coeff Array256.t) : coeff Array256.t =
{
  var rp1,rp2 : coeff Array256.t;
  rp1 <@ ___invntt_level6(rp);
  rp2 <- Array256.map (( * ) (incoeff 3303)) rp1;
  return rp2;
}

proc invntt(rp : coeff Array256.t) : coeff Array256.t = {
  var zeta0, zeta1, zeta0a, zeta1a, zeta0c, zeta1c, zeta0e, zeta1e, zeta0g, zeta1g, zeta0i, zeta1i, zeta0k, zeta1k, zeta0l, zeta1l, zeta0n, zeta1n, zeta0p, zeta1p, zeta0r, zeta1r, zeta0t, zeta1t : coeff Array16.t;
  var r0, r1, r2, r3, r4, r5, r6, r7 : coeff Array16.t;
  var r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a : coeff Array16.t;
  var r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b : coeff Array16.t;
  var r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c : coeff Array16.t;
  var r0d, r1d, r2d, r3d, r4d, r5d, r6d, r7d : coeff Array16.t;
  var r0e, r1e, r2e, r3e, r4e, r5e, r6e, r7e : coeff Array16.t;
  var r0f, r1f, r2f, r3f, r4f, r5f, r6f, r7f : coeff Array16.t;
  var r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g : coeff Array16.t;
  var r0h, r1h, r2h, r3h, r4h, r5h, r6h, r7h : coeff Array16.t;
  var r0i, r1i, r2i, r3i, r4i, r5i, r6i, r7i : coeff Array16.t;
  var r0j, r1j, r2j, r3j, r4j, r5j, r6j, r7j : coeff Array16.t;
  var r0k, r1k, r2k, r3k, r4k, r5k, r6k, r7k : coeff Array16.t;
  var r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l : coeff Array16.t;
  var r0m, r1m, r2m, r3m, r4m, r5m, r6m, r7m : coeff Array16.t;
  var r0n, r1n, r2n, r3n, r4n, r5n, r6n, r7n : coeff Array16.t;
  var r0o, r1o, r2o, r3o, r4o, r5o, r6o, r7o : coeff Array16.t;
  var r0p, r1p, r2p, r3p, r4p, r5p, r6p, r7p : coeff Array16.t;
  var r0q, r1q, r2q, r3q, r4q, r5q, r6q, r7q : coeff Array16.t;
  var r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r : coeff Array16.t;
  var r0s, r1s, r2s, r3s, r4s, r5s, r6s, r7s : coeff Array16.t;
  var r0t, r1t, r2t, r3t, r4t, r5t, r6t, r7t : coeff Array16.t;
  var r0u, r1u, r2u, r3u, r4u, r5u, r6u, r7u : coeff Array16.t;
  var rp1,rp2,rp3,rp4,rp5,rp6,rp7,rp8,rp9,rp10,rp11,rp12,rp13,rp14,rp15,rp16 : coeff Array256.t;

  (**** LEFT-HALF*****)
  
    (* level 0 *)
    zeta0 <- Array16.of_list witness [incoeff 1175 ; incoeff 394 ; incoeff 2300 ; incoeff 2117 ; incoeff 2443 ; incoeff 1179 ; incoeff 2303 ; incoeff 2237 ; incoeff 735 ; incoeff 2768 ; incoeff 2572 ; incoeff 3010; incoeff 1684 ; incoeff 780 ; incoeff 109 ; incoeff 1031];
    zeta1 <- Array16.of_list witness [incoeff 2444 ; incoeff 1219 ; incoeff 1455 ; incoeff 1607 ; incoeff 554 ; incoeff 2186 ; incoeff 2926 ; incoeff 525 ; incoeff 863 ; incoeff 1230 ; incoeff 556 ; incoeff 2266 ; incoeff 1239 ; incoeff 2954 ; incoeff 1292 ; incoeff 1745];

    r0 <- P2C rp 0;
    r1 <- P2C rp 1;
    r2 <- P2C rp 2;
    r3 <- P2C rp 3;
    r4 <- P2C rp 4;
    r5 <- P2C rp 5;
    r6 <- P2C rp 6;
    r7 <- P2C rp 7;

    (r0a, r1a, r4a, r5a, r2a, r3a, r6a, r7a) <@ __invntt___butterfly64x(r0, r1, r4, r5, r2, r3, r6, r7, zeta0, zeta1);

    (* level 1 *)
    zeta1a <- Array16.of_list witness [ incoeff 2419 ; incoeff 2102 ; incoeff 219 ; incoeff 855 ; incoeff 2681 ; incoeff 1848 ; incoeff 712 ; incoeff 682 ; incoeff 927 ; incoeff 1795 ; incoeff 461 ; incoeff 1891 ; incoeff 2877 ; incoeff 2522 ; incoeff 1894 ; incoeff 1010 ];

    (r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b) <@ __invntt___butterfly64x(r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a, zeta1a, zeta1a);
    
    (r0c,r1c) <- shuffle1 r0b r1b;
    (r2c,r3c) <- shuffle1 r2b r3b;
    (r4c,r5c) <- shuffle1 r4b r5b;
    (r6c,r7c) <- shuffle1 r6b r7b;

    (* level 2 *)
    zeta1c <- Array16.of_list witness [ incoeff 2508 ; incoeff 2508; incoeff 1355 ; incoeff 1355; incoeff 450 ; incoeff 450; incoeff 936; incoeff 936 ; incoeff 447; incoeff 447 ; incoeff 2794; incoeff 2794 ; incoeff 1235; incoeff 1235 ; incoeff 1903; incoeff 1903 ];

    (r0d, r2d, r4d, r6d, r1d, r3d, r5d, r7d) <@ __invntt___butterfly64x(r0c, r2c, r4c, r6c, r1c, r3c, r5c, r7c, zeta1c, zeta1c);

    (r0e,r2e) <- shuffle2 r0d r2d;
    (r4e,r6e) <- shuffle2 r4d r6d;
    (r1e,r3e) <- shuffle2 r1d r3d;
    (r5e,r7e) <- shuffle2 r5d r7d;

    (* level 3 *)
    zeta1e <- Array16.of_list witness [ incoeff 1583; incoeff 1583; incoeff 1583; incoeff 1583 ; incoeff 2760; incoeff 2760; incoeff 2760; incoeff 2760 ; incoeff 69 ; incoeff 69; incoeff 69; incoeff 69; incoeff 543; incoeff 543; incoeff 543; incoeff 543 ];

    (r0f, r4f, r1f, r5f, r2f, r6f, r3f, r7f) <@ __invntt___butterfly64x(r0e, r4e, r1e, r5e, r2e, r6e, r3e, r7e, zeta1e, zeta1e);

    (r0g,r4g) <- shuffle4 r0f r4f;
    (r1g,r5g) <- shuffle4 r1f r5f;
    (r2g,r6g) <- shuffle4 r2f r6f;
    (r3g,r7g) <- shuffle4 r3f r7f;

    (* level 4 *)
    zeta1g <- Array16.of_list witness [ incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481;incoeff 2481; incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432;incoeff 1432 ];

    (r0h, r1h, r2h, r3h, r4h, r5h, r6h, r7h) <@ __invntt___butterfly64x(r0g, r1g, r2g, r3g, r4g, r5g, r6g, r7g, zeta1g, zeta1g);

    (r0i,r1i) <- shuffle8 r0h r1h;
    (r2i,r3i) <- shuffle8 r2h r3h;
    (r4i,r5i) <- shuffle8 r4h r5h;
    (r6i,r7i) <- shuffle8 r6h r7h;

    (* level 5 *)
    zeta1i <- Array16.init (fun i => incoeff 40);

    (r0j, r2j, r4j, r6j, r1j, r3j, r5j, r7j) <@ __invntt___butterfly64x(r0i, r2i, r4i, r6i, r1i, r3i, r5i, r7i, zeta1i, zeta1i);

    rp1 <- PUC rp  0 r0j;
    rp2 <- PUC rp1 1 r2j;
    rp3 <- PUC rp2 2 r4j;
    rp4 <- PUC rp3 3 r6j;
    rp5 <- PUC rp4 4 r1j;
    rp6 <- PUC rp5 5 r3j;
    rp7 <- PUC rp6 6 r5j;
    rp8 <- PUC rp7 7 r7j;
  
  (**** RIGHT-HALF*****)
  
    (* level 0 *)
    zeta0k <- Array16.of_list witness [incoeff 2688 ; incoeff 992; incoeff 941; incoeff 1021; incoeff 642; incoeff 2377; incoeff 1540; incoeff 1678; incoeff 279; incoeff 1173; incoeff 3096; incoeff 667; incoeff 2229; incoeff 2606; incoeff 680; incoeff 568 ];
    zeta1k <- Array16.of_list witness [incoeff 3061 ; incoeff 2596 ; incoeff 892 ; incoeff 2390 ; incoeff 1868 ; incoeff 1482 ; incoeff 540 ; incoeff 1626; incoeff 314 ; incoeff 2573 ; incoeff 48 ; incoeff 1920 ; incoeff 1041 ; incoeff 1692 ; incoeff 2746 ; incoeff 3312 ];

    r0k <- P2C rp 8;
    r1k <- P2C rp 9;
    r2k <- P2C rp 10;
    r3k <- P2C rp 11;
    r4k <- P2C rp 12;
    r5k <- P2C rp 13;
    r6k <- P2C rp 14;
    r7k <- P2C rp 15;

    (r0l, r1l, r4l, r5l, r2l, r3l, r6l, r7l) <@ __invntt___butterfly64x(r0k, r1k, r4k, r5k, r2k, r3k, r6k, r7k, zeta0k, zeta1k);

    (* level 1 *)
    zeta1l <-  Array16.of_list witness
             [ incoeff 1414 ; incoeff 2009 ; incoeff 3296 ; incoeff 464 ; incoeff 2697 ; incoeff 816 ; incoeff 1352 ; incoeff 2679 ; incoeff 1274 ; incoeff 1052 ; incoeff 1025 ; incoeff 2132 ; incoeff 1573 ; incoeff 76 ; incoeff 2998 ; incoeff 3040 ];

    (r0m, r1m, r2m, r3m, r4m, r5m, r6m, r7m) <@ __invntt___butterfly64x(r0l, r1l, r2l, r3l, r4l, r5l, r6l, r7l, zeta1l, zeta1l);
    
    (r0n,r1n) <- shuffle1 r0m r1m;
    (r2n,r3n) <- shuffle1 r2m r3m;
    (r4n,r5n) <- shuffle1 r4m r5m;
    (r6n,r7n) <- shuffle1 r6m r7m;

    (* level 2 *)
    zeta1n <- Array16.of_list witness
             [ incoeff 1996 ; incoeff 1996; incoeff 1089 ; incoeff 1089; incoeff 3273 ; incoeff 3273; incoeff 283 ; incoeff 283; incoeff 1853 ; incoeff 1853; incoeff 1990 ; incoeff 1990; incoeff 882 ; incoeff 882; incoeff 3033; incoeff 3033 ];

    (r0o, r2o, r4o, r6o, r1o, r3o, r5o, r7o) <@ __invntt___butterfly64x(r0n, r2n, r4n, r6n, r1n, r3n, r5n, r7n, zeta1n, zeta1n);

    (r0p,r2p) <- shuffle2 r0o r2o;
    (r4p,r6p) <- shuffle2 r4o r6o;
    (r1p,r3p) <- shuffle2 r1o r3o;
    (r5p,r7p) <- shuffle2 r5o r7o;

    (* level 3 *)
    zeta1p <- Array16.of_list witness
             [ incoeff 2532 ; incoeff 2532; incoeff 2532; incoeff 2532; incoeff 3136 ; incoeff 3136; incoeff 3136; incoeff 3136; incoeff 1410 ; incoeff 1410; incoeff 1410; incoeff 1410; incoeff 2267; incoeff 2267; incoeff 2267; incoeff 2267 ];

    (r0q, r4q, r1q, r5q, r2q, r6q, r3q, r7q) <@ __invntt___butterfly64x(r0p, r4p, r1p, r5p, r2p, r6p, r3p, r7p, zeta1p, zeta1p);

    (r0r,r4r) <- shuffle4 r0q r4q;
    (r1r,r5r) <- shuffle4 r1q r5q;
    (r2r,r6r) <- shuffle4 r2q r6q;
    (r3r,r7r) <- shuffle4 r3q r7q;

    (* level 4 *)
    zeta1r <- Array16.of_list witness
             [ incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699;incoeff 2699 ; incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687;incoeff 687 ];

    (r0s, r1s, r2s, r3s, r4s, r5s, r6s, r7s) <@ __invntt___butterfly64x(r0r, r1r, r2r, r3r, r4r, r5r, r6r, r7r, zeta1r, zeta1r);

    (r0t,r1t) <- shuffle8 r0s r1s;
    (r2t,r3t) <- shuffle8 r2s r3s;
    (r4t,r5t) <- shuffle8 r4s r5s;
    (r6t,r7t) <- shuffle8 r6s r7s;

    (* level 5 *)
    zeta1t <- Array16.init (fun i => incoeff 749);

    (r0u, r2u, r4u, r6u, r1u, r3u, r5u, r7u) <@ __invntt___butterfly64x(r0t, r2t, r4t, r6t, r1t, r3t, r5t, r7t, zeta1t, zeta1t);
    
    rp9  <- PUC rp8  8  r0u;
    rp10 <- PUC rp9  9  r2u;
    rp11 <- PUC rp10 10 r4u;
    rp12 <- PUC rp11 11 r6u;
    rp13 <- PUC rp12 12 r1u;
    rp14 <- PUC rp13 13 r3u;
    rp15 <- PUC rp14 14 r5u;
    rp16 <- PUC rp15 15 r7u;

    (* level 6 *)
    rp <- rp16;
    zeta0 <- Array16.init (fun i => incoeff 1600);
  
    (r0,r1,r2,r3,r0b,r1b,r2b,r3b) <- (P2C rp 0, P2C rp 1, P2C rp 2, P2C rp 3, P2C rp 4, P2C rp 5, P2C rp 6, P2C rp 7);
    (r4,r5,r6,r7,r4b,r5b,r6b,r7b) <- (P2C rp 8, P2C rp 9, P2C rp 10, P2C rp 11, P2C rp 12, P2C rp 13, P2C rp 14, P2C rp 15);

    (r0a, r1a, r2a, r3a, r4a, r5a, r6a, r7a) <@ __invntt___butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta0, zeta0);
    
    (r0c, r1c, r2c, r3c, r4c, r5c, r6c, r7c) <@ __invntt___butterfly64x(r0b, r1b, r2b, r3b, r4b, r5b, r6b, r7b, zeta0, zeta0);
    
    rp1 <- CS2P [r0a;r1a;r2a;r3a;r0c;r1c;r2c;r3c;r4a;r5a;r6a;r7a;r4c;r5c;r6c;r7c];
    rp2 <- Array256.map (( * ) (incoeff 3303)) rp1;
    return rp2;
}

proc invntt0t6(r : coeff Array256.t) : coeff Array256.t = {
 var rp0,rp1,rp2,rp3,rp4,rp5,rp6;
 rp0 <@ __invntt_level0(r);
 rp1 <@ __invntt_level1(rp0);
 rp2 <@ __invntt_level2(rp1);
 rp3 <@ __invntt_level3(rp2);
 rp4 <@ __invntt_level4(rp3);
 rp5 <@ __invntt_level5(rp4);
 rp6 <@ __invntt_level6(rp5);
 return rp6;
}

proc invntt_bsrev(r : coeff Array256.t) : coeff Array256.t = {
  NTT_vars.r <- r;
  NTT_vars.zetas_inv <- NTT_Fq.zetas_inv;
  r <@ NTT_bsrev.invntt();
  return r;
 }

proc __cmplx_mulx16(are aim bre bim zetas: coeff Array16.t, sign: bool): coeff Array16.t * coeff Array16.t = {
 var rre, rim;
 rre <- Array16.init
   (fun i => (cmplx_mul (are.[i],aim.[i]) (bre.[i],bim.[i]) ((if sign then incoeff (-1) else incoeff 1) * zetas.[i])).`1);
 rim <- Array16.init
   (fun i => (cmplx_mul (are.[i],aim.[i]) (bre.[i],bim.[i]) ((if sign then incoeff (-1) else incoeff 1) * zetas.[i])).`2);
 return (rre,rim);
}

proc __basemul(r a b: coeff Array256.t): coeff Array256.t = {
 var are, aim, bre, bim, rre, rim, zetas;

 zetas <- Array16.of_list witness [ incoeff 17; incoeff 583; incoeff 1637; incoeff 2288; incoeff 1409; incoeff 3281; incoeff 756; incoeff 3015; incoeff 1703; incoeff 2789; incoeff 1847; incoeff 1461; incoeff 939; incoeff 2437; incoeff 733; incoeff 268 ];

 are <- P2C a 0;
 aim <- P2C a 1;
 bre <- P2C b 0;
 bim <- P2C b 1;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, false);
 r <- PUC r 0 rre;
 r <- PUC r 1 rim;
 are <- P2C a 2;
 aim <- P2C a 3;
 bre <- P2C b 2;
 bim <- P2C b 3;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, true);
 r <- PUC r 2 rre;
 r <- PUC r 3 rim;

 zetas <- Array16.of_list witness [ incoeff 2761; incoeff 2649; incoeff 723; incoeff 1100; incoeff 2662; incoeff 233; incoeff 2156; incoeff 3050; incoeff 1651; incoeff 1789; incoeff 952; incoeff 2687; incoeff 2308; incoeff 2388; incoeff 2337; incoeff 641 ];

 are <- P2C a 4;
 aim <- P2C a 5;
 bre <- P2C b 4;
 bim <- P2C b 5;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, false);
 r <- PUC r 4 rre;
 r <- PUC r 5 rim;
 are <- P2C a 6;
 aim <- P2C a 7;
 bre <- P2C b 6;
 bim <- P2C b 7;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, true);
 r <- PUC r 6 rre;
 r <- PUC r 7 rim;

 zetas <- Array16.of_list witness [ incoeff 1584; incoeff 2037; incoeff 375; incoeff 2090; incoeff 1063; incoeff 2773; incoeff 2099; incoeff 2466; incoeff 2804; incoeff 403; incoeff 1143; incoeff 2775; incoeff 1722; incoeff 1874; incoeff 2110; incoeff 885 ];

 are <- P2C a 8;
 aim <- P2C a 9;
 bre <- P2C b 8;
 bim <- P2C b 9;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, false);
 r <- PUC r 8 rre;
 r <- PUC r 9 rim;
 are <- P2C a 10;
 aim <- P2C a 11;
 bre <- P2C b 10;
 bim <- P2C b 11;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, true);
 r <- PUC r 10 rre;
 r <- PUC r 11 rim;

 zetas <- Array16.of_list witness [ incoeff 2298; incoeff 3220; incoeff 2549; incoeff 1645; incoeff 319; incoeff 757; incoeff 561; incoeff 2594; incoeff 1092; incoeff 1026; incoeff 2150; incoeff 886; incoeff 1212; incoeff 1029; incoeff 2935; incoeff 2154 ];

 are <- P2C a 12;
 aim <- P2C a 13;
 bre <- P2C b 12;
 bim <- P2C b 13;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, false);
 r <- PUC r 12 rre;
 r <- PUC r 13 rim;
 are <- P2C a 14;
 aim <- P2C a 15;
 bre <- P2C b 14;
 bim <- P2C b 15;
 (rre, rim) <@ __cmplx_mulx16(are, aim, bre, bim, zetas, true);
 r <- PUC r 14 rre;
 r <- PUC r 15 rim;

 return r;
}
}.

op basemul_avx2 (a b : poly): poly =
 Array256.init
  (fun i =>
    let i_l = i %% 16 in
    let i_z = i %/ 32 in
    let i_off = 32 * i_z in
    let zsign = Zq.exp (incoeff (-1)) (i_z %% 2) in
    let zeta_i = 64 + (i_z %/ 2 %% 2) + i_z %/ 4 * 32 + 2 * i_l in  
    if i = i_off + i_l
    then (cmplx_mul (a.[i_off+i_l],a.[i_off+i_l+16])
                    (b.[i_off+i_l],b.[i_off+i_l+16])
                    (zsign * NTT_Fq.zetas.[zeta_i])).`1
    else (cmplx_mul (a.[i_off+i_l],a.[i_off+i_l+16])
                    (b.[i_off+i_l],b.[i_off+i_l+16])
                    (zsign * NTT_Fq.zetas.[zeta_i])).`2).

hoare __basemul_h _a _b:
 NTT_AVX.__basemul: a =
 _a /\ b = _b ==> res = basemul_avx2 _a _b.
proof.
proc; simplify.
seq 15: (#pre /\ all (fun k => (basemul_avx2 _a _b).[k] = r.[k]) (iota_ 0 64)).
 inline*; wp; skip => |> &1 *.
 rewrite (P2CS r{1}) !PUC_i //=.
 by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE
     /= ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
seq 15:(#pre /\ all (fun k => (basemul_avx2 _a _b).[k] = r.[k]) (iota_ 64 64)).
 inline*; wp; skip => |> &m H; split.
  move: H; rewrite (P2CS r{m}) !PUC_i //=.
  by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
      ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
 rewrite (P2CS r{m}) !PUC_i //=.
 by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
      ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
seq 15:(#pre /\ all (fun k => (basemul_avx2 _a _b).[k] = r.[k]) (iota_ 128 64)).
 inline*; wp; skip => |> &m H1 H2; split.
  split. 
   move: H1; rewrite (P2CS r{m}) !PUC_i //=.
   by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
        ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
  move: H2; rewrite (P2CS r{m}) !PUC_i //=.
  by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
      ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
 rewrite (P2CS r{m}) !PUC_i //=.
 by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
     ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
seq 15:(#pre /\ all (fun k => (basemul_avx2 _a _b).[k] = r.[k]) (iota_ 192 64)).
 inline*; wp; skip => |> &m H1 H2 H3; split.
  split.
   split.
    move: H1; rewrite (P2CS r{m}) !PUC_i //=.
    by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
      ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
   move: H2; rewrite (P2CS r{m}) !PUC_i //=.
   by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
        ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
  move: H3; rewrite (P2CS r{m}) !PUC_i //=.
  by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
      ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
 rewrite (P2CS r{m}) !PUC_i //=.
 by rewrite /basemul_avx2 /= NTT_Fq.zetasE -iotaredE /=
      ?ZqField.expr0 ?ZqField.expr1 !initiE //= /P2C /pchunk /=.
skip => |> &m H0 H1 H2 H3.
apply Array256.all_eq_eq; rewrite /all_eq iotaredE.
rewrite (_:256=64+64+64+64) 1://.
by rewrite !iota_add 1..7:// /= !all_cat /#. 
qed.

lemma __basemul_ll: islossless NTT_AVX.__basemul by islossless.

phoare __basemul_ph _a _b:
 [ NTT_AVX.__basemul: a =
   _a /\ b = _b ==> res = basemul_avx2 _a _b ] = 1%r.
proof. by conseq __basemul_ll (__basemul_h _a _b). qed.


op basemul_zetas (a b : poly): poly =
 Array256.init
  (fun i => let ii = i %/ 2 in
            let zsign = Zq.exp (incoeff (-1)) (ii %% 2) in
            if i %% 2 = 0 then
            (cmplx_mul (a.[2 * ii], a.[2 * ii + 1]) (b.[2 * ii], b.[2 * ii + 1]) (zsign*NTT_Fq.zetas.[64+ii%/2])).`1
            else
            (cmplx_mul (a.[2 * ii], a.[2 * ii + 1]) (b.[2 * ii], b.[2 * ii + 1]) (zsign*NTT_Fq.zetas.[64+ii%/2])).`2).


lemma basemul_zetasE a b:
 basemul a b = basemul_zetas a b.
proof.
rewrite /basemul /basemul_zetas tP => i Hi.
rewrite !initiE //=.
case: (i%%2=0) => RI.
 congr; congr.
 have ->: ZqRing.exp = Zq.exp by done.
 case: (i %/ 2 %% 2 = 0).
  move=> E; rewrite E ZqField.expr0 ZqField.mul1r.
  rewrite NTT_Fq.zetavals1' 1:/# //; congr; smt().
 move=> E'; have E: i %/ 2 %% 2 = 1 by smt().
 rewrite E ZqField.expr1.
 rewrite NTT_Fq.zetavals2' 1:/# // Zq.incoeffN  ZqField.mulN1r /#.
congr; congr.
have ->: ZqRing.exp = Zq.exp by done.
case: (i %/ 2 %% 2 = 0).
 move=> E; rewrite E ZqField.expr0 ZqField.mul1r.
 rewrite NTT_Fq.zetavals1' 1:/# //; congr. smt().
move=> E'; have E: i %/ 2 %% 2 = 1 by smt().
rewrite E ZqField.expr1 NTT_Fq.zetavals2' 1:/# // Zq.incoeffN  ZqField.mulN1r /#.
qed.

lemma basemul_avx2E (a b: poly):
 perm_ntt perm_nttpack128 (basemul_avx2 a b)
 = basemul (perm_ntt perm_nttpack128 a) (perm_ntt perm_nttpack128 b).
proof.
rewrite basemul_zetasE.
by apply Array256.all_eq_eq; rewrite /all_eq /basemul_zetas /basemul_avx2 /perm_nttpack128 /perm_nttunpack128 /perm_ntt /=. 
qed.

(* equivalence between full-inline-SSA and level-by-level ntt avx2 *)
lemma ntt0t6_ntt : 
  equiv [ NTT_AVX.ntt ~ NTT_AVX.ntt0t6 : rp{1}=r{2} ==> ={res}].
proof.
proc; simplify.
seq 6 1: (rp{1}=rp0{2}).
 by inline *; auto. 
(* level 1 *) (* [loc(zeta1k)..loc(r0l)] - (loc(zeta1k)-loc(r0a)-1) *)
swap{1} [46..55] -35.
seq 20 1: (CS2P [r0a;r1a;r2a;r3a;r4a;r5a;r6a;r7a;r0l;r1l;r2l;r3l;r4l;r5l;r6l;r7l]{1} = rp1{2}).
 by inline *; auto.
(* level 2 *) (* [loc(zeta1m)..loc(r0n)] - (loc(zeta1m)-loc(r0c)-1) *)
swap{1} [36..41] -29.
seq 12 1: (CS2P [r0c;r4c;r1c;r5c;r2c;r6c;r3c;r7c;r0n;r4n;r1n;r5n;r2n;r6n;r3n;r7n]{1} = rp2{2}).
 by inline *; auto => /> *; rewrite !P2C_i.
(* level 3 *) (* [loc(zeta1o)..loc(r0p)] - (loc(zeta1o)-loc(r0e)-1) *)
swap{1} [30..35] -23.
seq 12 1: (CS2P [r0e;r2e;r4e;r6e;r1e;r3e;r5e;r7e;r0p;r2p;r4p;r6p;r1p;r3p;r5p;r7p]{1} = rp3{2}).
 by inline *; auto => /> *; rewrite !P2C_i.
(* level 4 *) (* [loc(zeta1q)..loc(r0r)] - (loc(zeta1q)-loc(r0g)-1) *)
swap{1} [24..29] -17.
seq 12 1: (CS2P [r0g;r1g;r2g;r3g;r4g;r5g;r6g;r7g;r0r;r1r;r2r;r3r;r4r;r5r;r6r;r7r]{1} = rp4{2}).
 by inline *; auto => /> *; rewrite !P2C_i.
(* level 5 *) (* [loc(zeta1s)..loc(r0t)] - (loc(zeta1s)-loc(r0i)-1) *)
swap{1} [18..23] -11.
seq 12 1: (CS2P [r0i;r4i;r1i;r5i;r2i;r6i;r3i;r7i;r0t;r4t;r1t;r5t;r2t;r6t;r3t;r7t]{1} = rp5{2}).
 by inline *; auto => /> *; rewrite !P2C_i.
(* level 6 *) (* [loc(zeta2t)..loc(r0u)] - (loc(zeta2t)-loc(r0j)-1) *)
swap{1} [12..14] -8.
seq 6 1: (CS2P [r0j;r4j;r1j;r5j;r2j;r6j;r3j;r7j;r0u;r4u;r1u;r5u;r2u;r6u;r3u;r7u]{1} = rp6{2}).
 by inline *; auto => /> *; rewrite !P2C_i.
(* return *)
inline *; auto => /> &1.
by rewrite (P2CS rp{1}) !PUC_i.
qed.

lemma ntt_avx_0_ll : islossless NTT_AVX.__ntt_level0 by islossless.
lemma ntt_avx_1_ll : islossless NTT_AVX.__ntt_level1 by islossless.
lemma ntt_avx_2_ll : islossless NTT_AVX.__ntt_level2 by islossless.
lemma ntt_avx_3_ll : islossless NTT_AVX.__ntt_level3 by islossless.
lemma ntt_avx_4_ll : islossless NTT_AVX.__ntt_level4 by islossless.
lemma ntt_avx_5_ll : islossless NTT_AVX.__ntt_level5 by islossless.
lemma ntt_avx_6_ll : islossless NTT_AVX.__ntt_level6 by islossless.

hoare ntt_avx_0 r:
  NTT_AVX.__ntt_level0 : rp = r ==> res = r_avx2_ntt NTT_Fq.zetas r 0.
proof.
proc; inline *; wp; auto => /> /=.
rewrite NTT_Fq.zetasE r_avx2_ntt_spec => />. 
apply tP_red256 => i /=.
do 255! (move => Hi; case Hi; first done).
by move=> ->; rewrite !initiE.
qed.

lemma ntt_avx_0_pr r:
  phoare [NTT_AVX.__ntt_level0 : rp = r ==> res = r_avx2_ntt NTT_Fq.zetas r 0] = 1%r.
proof. conseq ntt_avx_0_ll (ntt_avx_0 r) => />. qed.

hoare ntt_avx_1 r:
  NTT_AVX.__ntt_level1 : rp = r ==> res = r_avx2_ntt NTT_Fq.zetas r 1.
proof.
proc; inline *; wp; auto => />.
rewrite NTT_Fq.zetasE r_avx2_ntt_spec => />.
apply tP_red256 => i /=.
do 255! (move => Hi; case Hi; first done).
by move=> ->; rewrite !initiE.
qed.

lemma ntt_avx_1_pr r:
  phoare [NTT_AVX.__ntt_level1 : rp = r ==> res = r_avx2_ntt NTT_Fq.zetas r 1] = 1%r.
proof. by conseq ntt_avx_1_ll (ntt_avx_1 r). qed.

op perm_level2 : int list =
  [0;1;2;3;4;5;6;7;16;17;18;19;20;21;22;23;32;33;34;35;36;37;38;39;48;49;50;51;52;53;54;55;64;65;66;67;68;69;70;71;80;81;82;83;84;85;86;87;96;97;98;99;100;101;102;103;112;113;114;115;116;117;118;119;8;9;10;11;12;13;14;15;24;25;26;27;28;29;30;31;40;41;42;43;44;45;46;47;56;57;58;59;60;61;62;63;72;73;74;75;76;77;78;79;88;89;90;91;92;93;94;95;104;105;106;107;108;109;110;111;120;121;122;123;124;125;126;127] axiomatized by perm_level2E.

hoare ntt_avx_2 r:
  NTT_AVX.__ntt_level2 : rp = r ==> perm_ntt perm_level2 res = r_avx2_ntt NTT_Fq.zetas r 2.
proof.
proc; inline *; wp; auto => />.
rewrite NTT_Fq.zetasE r_avx2_ntt_spec => />.
apply tP_red256 => i /=.
do 255! (move => [->|];
first by (rewrite /perm_ntt /perm_level2 initiE 1:// /= /CS2P initiE 1:// /= !shuffle8E /P2C /pchunk /=)).
by move=> ->; rewrite !perm_level2E !shuffle8E !initiE.
qed.

lemma ntt_avx_2_pr r:
  phoare [NTT_AVX.__ntt_level2 : rp = r ==> perm_ntt perm_level2 res = r_avx2_ntt NTT_Fq.zetas r 2] = 1%r.
proof. by conseq ntt_avx_2_ll (ntt_avx_2 r). qed.

op perm_level3 : int list =
  [0;1;2;3;16;17;18;19;32;33;34;35;48;49;50;51;64;65;66;67;80;81;82;83;96;97;98;99;112;113;114;115;4;5;6;7;20;21;22;23;36;37;38;39;52;53;54;55;68;69;70;71;84;85;86;87;100;101;102;103;116;117;118;119;8;9;10;11;24;25;26;27;40;41;42;43;56;57;58;59;72;73;74;75;88;89;90;91;104;105;106;107;120;121;122;123;12;13;14;15;28;29;30;31;44;45;46;47;60;61;62;63;76;77;78;79;92;93;94;95;108;109;110;111;124;125;126;127] axiomatized by perm_level3E.

hoare ntt_avx_3 r:
  NTT_AVX.__ntt_level3 : perm_ntt perm_level2 rp = r ==> perm_ntt perm_level3 res = r_avx2_ntt NTT_Fq.zetas r 3.
proof.
proc; inline *; wp; auto => /> &1. 
rewrite NTT_Fq.zetasE r_avx2_ntt_spec => />.
apply tP_red256 => i /=.
do 255! (move => [->|];
first by (rewrite /perm_ntt /perm_level2 /perm_level3 initiE 1:// /= /CS2P initiE 1:// /= !shuffle4E /P2C /pchunk /=)).
by move=> ->; rewrite /perm_level2 /perm_level3 !shuffle4E !initiE.
qed.

lemma ntt_avx_3_pr r:
  phoare [NTT_AVX.__ntt_level3 : perm_ntt perm_level2 rp = r ==> perm_ntt perm_level3 res = r_avx2_ntt NTT_Fq.zetas r 3] = 1%r.
proof. by conseq ntt_avx_3_ll (ntt_avx_3 r). qed.

op perm_level4 : int list =
  [0;1;16;17;32;33;48;49;64;65;80;81;96;97;112;113;2;3;18;19;34;35;50;51;66;67;82;83;98;99;114;115;4;5;20;21;36;37;52;53;68;69;84;85;100;101;116;117;6;7;22;23;38;39;54;55;70;71;86;87;102;103;118;119;8;9;24;25;40;41;56;57;72;73;88;89;104;105;120;121;10;11;26;27;42;43;58;59;74;75;90;91;106;107;122;123;12;13;28;29;44;45;60;61;76;77;92;93;108;109;124;125;14;15;30;31;46;47;62;63;78;79;94;95;110;111;126;127] axiomatized by perm_level4E.

hoare ntt_avx_4 r:
  NTT_AVX.__ntt_level4 : perm_ntt perm_level3 rp = r ==> perm_ntt perm_level4 res = r_avx2_ntt NTT_Fq.zetas r 4.
proof.
proc; inline *; wp; auto => /> &1. 
rewrite NTT_Fq.zetasE r_avx2_ntt_spec => />.
apply tP_red256 => i /=.
do 255! (move => [->|];
first by (rewrite /perm_ntt /perm_level3 /perm_level4 initiE 1:// /= /CS2P initiE 1:// /= /shuffle2 /P2C /pchunk /=)).
by move=> ->; rewrite /perm_level3 /perm_level4 /shuffle2 !initiE.
qed.

lemma ntt_avx_4_pr r:
  phoare [NTT_AVX.__ntt_level4 : perm_ntt perm_level3 rp = r ==> perm_ntt perm_level4 res = r_avx2_ntt NTT_Fq.zetas r 4] = 1%r.
proof. by conseq ntt_avx_4_ll (ntt_avx_4 r). qed.

op perm_level5 : int list =
  [0;16;32;48;64;80;96;112;1;17;33;49;65;81;97;113;2;18;34;50;66;82;98;114;3;19;35;51;67;83;99;115;4;20;36;52;68;84;100;116;5;21;37;53;69;85;101;117;6;22;38;54;70;86;102;118;7;23;39;55;71;87;103;119;8;24;40;56;72;88;104;120;9;25;41;57;73;89;105;121;10;26;42;58;74;90;106;122;11;27;43;59;75;91;107;123;12;28;44;60;76;92;108;124;13;29;45;61;77;93;109;125;14;30;46;62;78;94;110;126;15;31;47;63;79;95;111;127] axiomatized by perm_level5E.

hoare ntt_avx_5 r:
  NTT_AVX.__ntt_level5 : perm_ntt perm_level4 rp = r ==> perm_ntt perm_level5 res = r_avx2_ntt NTT_Fq.zetas r 5.
proof.
proc; inline *; wp; auto => /> &1. 
rewrite NTT_Fq.zetasE r_avx2_ntt_spec => />.
apply tP_red256 => i /=.
do 255! (move => [->|];
first by (rewrite /perm_ntt /perm_level4 /perm_level5 initiE 1:// /= /CS2P initiE 1:// /= /shuffle1 /P2C /pchunk /=)).
by move=> ->; rewrite /perm_level4 /perm_level5 /shuffle1 !initiE.
qed.

lemma ntt_avx_5_pr r:
  phoare [NTT_AVX.__ntt_level5 : perm_ntt perm_level4 rp = r ==> perm_ntt perm_level5 res = r_avx2_ntt NTT_Fq.zetas r 5] = 1%r.
proof. by conseq ntt_avx_5_ll (ntt_avx_5 r). qed.

hoare ntt_avx_6 r:
  NTT_AVX.__ntt_level6 : perm_ntt perm_level5 rp = r ==> perm_ntt perm_nttpack128 res = r_avx2_ntt NTT_Fq.zetas r 6.
proof.
proc; inline *; wp; auto => /> &1. 
rewrite NTT_Fq.zetasE r_avx2_ntt_spec => />.
apply tP_red256 => i /=.
do 255! (move => [->|];
first by (rewrite /perm_ntt /perm_level5 /perm_nttpack128 initiE 1:// /= /CS2P initiE 1:// /= /P2C /pchunk /=)).
by move=> ->; rewrite /perm_level5 /perm_nttpack128 !initiE.
qed.

lemma ntt_avx_6_pr r:
  phoare [NTT_AVX.__ntt_level6 : perm_ntt perm_level5 rp = r ==> perm_ntt perm_nttpack128 res = r_avx2_ntt NTT_Fq.zetas r 6] = 1%r.
proof. by conseq ntt_avx_6_ll (ntt_avx_6 r). qed.


(** Main Theorems in this module: abstract coeff-based AVX implementation and original NTT specification are equivalent **)
lemma ntt_avx_equiv : 
     equiv [ NTT_AVX.ntt ~ NTT_AVX.ntt_bsrev:
          rp{1}=r{2} ==> perm_ntt perm_nttpack128 res{1} = res{2}].
proof.
transitivity NTT_avx2.ntt
  (rp{1}=NTT_avx2.r{2} /\  NTT_avx2.zetas{2}=NTT_Fq.zetas ==> perm_ntt perm_nttpack128 res{1}=res{2})
  (NTT_avx2.r{1}=r{2} /\ NTT_avx2.zetas{1}=NTT_Fq.zetas ==> ={res})=> //;
 [ by ( move => /> &2; exists r{2} NTT_Fq.zetas)
 | | by (symmetry; proc*; inline NTT_AVX.ntt_bsrev;
         wp; call avx2_ntt; wp; skip => /> &1 &2)].
proc*.
transitivity{1} { r <@ NTT_AVX.ntt0t6(r); }
  (rp{1}=r{2} ==> ={r})
  (r{1} = NTT_avx2.r{2} /\ NTT_avx2.zetas{2}=NTT_Fq.zetas  ==> perm_ntt perm_nttpack128 r{1}=r{2}) => //.
  by move => /> &1 /#. 
 by call ntt0t6_ntt.
inline NTT_AVX.ntt0t6 NTT_avx2.ntt.
(*level 0*)
rcondt{2} 2; auto => />.
seq 2 3 : (NTT_avx2.zetas{2}=NTT_Fq.zetas /\ rp0{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=1 ).
ecall {1} (ntt_avx_0_pr r0{1}).
 by auto => /> *.
(*level 1*)
exlim NTT_avx2.r{2} => r0.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas{2}=NTT_Fq.zetas /\ rp1{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=2 ).
 by ecall {1} (ntt_avx_1_pr r0); auto.
(*level 2*)
exlim NTT_avx2.r{2} => r1.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas{2}=NTT_Fq.zetas /\ perm_ntt perm_level2 rp2{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=3 ).
 by call{1} (ntt_avx_2_pr r1); auto.
(*level 3*)
exlim NTT_avx2.r{2} => r2.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas{2}=NTT_Fq.zetas /\ perm_ntt perm_level3 rp3{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=4 ).
 by call{1} (ntt_avx_3_pr r2); auto.
(*level 4*)
exlim NTT_avx2.r{2} => r3.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas{2}=NTT_Fq.zetas /\ perm_ntt perm_level4 rp4{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=5 ).
 by call{1} (ntt_avx_4_pr r3); auto.
(*level 5*)
exlim NTT_avx2.r{2} => r4.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas{2}=NTT_Fq.zetas /\ perm_ntt perm_level5 rp5{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=6 ).
 by call{1} (ntt_avx_5_pr r4); auto.
(*level 6*)
exlim NTT_avx2.r{2} => r5.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas{2}=NTT_Fq.zetas /\ perm_ntt perm_nttpack128 rp6{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=7 ).
 by call{1} (ntt_avx_6_pr r5); auto.
(*exit*)
by rcondf{2} 1; auto => />.
qed.

hoare ntt_bsrev_h _r: 
   NTT_AVX.ntt_bsrev:
    r = _r ==> res = ntt _r.
proof.
proc.
ecall (bsrev_ntt_spec NTT_vars.r).
wp; skip => /> rr.
by apply imp_ntt_spec.
qed.

hoare ntt_avx_h _r:
 NTT_AVX.ntt : rp = _r ==> perm_ntt perm_nttpack128 res = ntt _r.
proof.
bypr => // &m ->.
have <-: Pr[NTT_AVX.ntt_bsrev(_r) @ &m : res <> ntt _r] = 0%r.
 byphoare (_:r=_r ==> _) => //; hoare => //.
 by conseq (ntt_bsrev_h _r).
byequiv => //.
by conseq ntt_avx_equiv.
qed.

lemma ntt_avx_ll: islossless  NTT_AVX.ntt by islossless.

phoare ntt_avx_spec _r:
 [ NTT_AVX.ntt : rp = _r ==> perm_ntt perm_nttpack128 res = ntt _r ] = 1%r.
proof. by conseq ntt_avx_ll (ntt_avx_h _r). qed.

(* equivalence between full-inline-SSA and level-by-level ntt avx2 (inverse) *)
lemma invntt0t6_invntt : 
  equiv [ NTT_AVX.invntt ~ NTT_AVX.invntt0t6 : rp{1}=r{2} ==> ={res}].
proof.
proc; simplify.
(* level 0 *) (* [loc(zeta0k)..loc(r0l)] - (loc(zeta0k)-loc(r0a)-1) *)
swap{1} [46..56] -34.
seq 22 1: (CS2P [r0a;r1a;r4a;r5a;r2a;r3a;r6a;r7a;r0l;r1l;r4l;r5l;r2l;r3l;r6l;r7l]{1} = rp0{2}).
  by inline *; auto.
(* level 1 *) (* [loc(zeta1l)..loc(r7n)] - (loc(zeta1l)-loc(r7c)-1) *)
swap{1} [35..40] -28.
seq 12 1: (CS2P [r0c;r1c;r2c;r3c;r4c;r5c;r6c;r7c;r0n;r1n;r2n;r3n;r4n;r5n;r6n;r7n]{1} = rp1{2}).
  by inline *; auto => /> *; rewrite !P2C_i => />.
(* level 2 *) (* [loc(zeta1n)..loc(r7p)] - (loc(zeta1n)-loc(r7e)-1) *)
swap{1} [29..34] -22.
seq 12 1: (CS2P [r0e;r2e;r4e;r6e;r1e;r3e;r5e;r7e;r0p;r2p;r4p;r6p;r1p;r3p;r5p;r7p]{1} = rp2{2}).
  by inline *; auto => />*; rewrite !P2C_i => />.
(* level 3 *) (* [loc(zeta1p)..loc(r7r)] - (loc(zeta1p)-loc(r7g)-1) *)
swap{1} [23..28] -16.
seq 12 1: (CS2P [r0g;r4g;r1g;r5g;r2g;r6g;r3g;r7g;r0r;r4r;r1r;r5r;r2r;r6r;r3r;r7r]{1} = rp3{2}).
 by inline *; auto => /> *; rewrite !P2C_i => />.
(* level 4 *) (* [loc(zeta1r)..loc(r7t)] - (loc(zeta1r)-loc(r7i)-1) *)
swap{1} [17..22] -10.
seq 12 1: (CS2P [r0i;r1i;r2i;r3i;r4i;r5i;r6i;r7i;r0t;r1t;r2t;r3t;r4t;r5t;r6t;r7t]{1} = rp4{2}).
 by inline *; auto => /> *; rewrite !P2C_i => />.
(* level 5 *)
seq 21 1: (rp{1} = rp5{2}).
  by inline *; auto => />*; rewrite !P2C_i => />; rewrite P2CS !PUC_i => />. 
by inline *; auto => />*.
qed.

lemma invntt_avx_0_ll : islossless NTT_AVX.__invntt_level0 by islossless.
lemma invntt_avx_1_ll : islossless NTT_AVX.__invntt_level1 by islossless.
lemma invntt_avx_2_ll : islossless NTT_AVX.__invntt_level2 by islossless.
lemma invntt_avx_3_ll : islossless NTT_AVX.__invntt_level3 by islossless.
lemma invntt_avx_4_ll : islossless NTT_AVX.__invntt_level4 by islossless.
lemma invntt_avx_5_ll : islossless NTT_AVX.__invntt_level5 by islossless.
lemma _invntt_avx_6_ll : islossless NTT_AVX.___invntt_level6 by islossless.
lemma invntt_avx_6_ll : islossless NTT_AVX.__invntt_level6 by islossless.

op perm_inv_level0 : int list =
  [0;16;64;80;32;48;96;112;1;17;65;81;33;49;97;113;2;18;66;82;34;50;98;114;3;19;67;83;35;51;99;115;4;20;68;84;36;52;100;116;5;21;69;85;37;53;101;117;6;22;70;86;38;54;102;118;7;23;71;87;39;55;103;119;8;24;72;88;40;56;104;120;9;25;73;89;41;57;105;121;10;26;74;90;42;58;106;122;11;27;75;91;43;59;107;123;12;28;76;92;44;60;108;124;13;29;77;93;45;61;109;125;14;30;78;94;46;62;110;126;15;31;79;95;47;63;111;127]
 axiomatized by perm_inv_level0E.

hoare invntt_avx_0 r:
  NTT_AVX.__invntt_level0 : perm_ntt perm_nttpack128 rp = r ==> perm_ntt perm_inv_level0 res = r_avx2_invntt NTT_Fq.zetas_inv r 0.
proof.
proc; inline *; wp; auto => /> /= &hr.
rewrite NTT_Fq.zetas_invE r_avx2_invntt_spec => />. 
apply tP_red256 => i /=.
do 256!(try (move => Hi; case Hi => />); first by rewrite /CS2P !initiE /P2C /pchunk /punchunk /perm_nttpack128 /perm_inv_level0 => />).
qed.

lemma invntt_avx_0_pr r:
  phoare [NTT_AVX.__invntt_level0 : perm_ntt perm_nttpack128 rp = r ==> perm_ntt perm_inv_level0 res = r_avx2_invntt NTT_Fq.zetas_inv r 0] = 1%r.
proof. by conseq invntt_avx_0_ll (invntt_avx_0 r). qed.

op perm_inv_level1 : int list =
  [0;1;32;33;64;65;96;97;16;17;48;49;80;81;112;113;2;3;34;35;66;67;98;99;18;19;50;51;82;83;114;115;4;5;36;37;68;69;100;101;20;21;52;53;84;85;116;117;6;7;38;39;70;71;102;103;22;23;54;55;86;87;118;119;8;9;40;41;72;73;104;105;24;25;56;57;88;89;120;121;10;11;42;43;74;75;106;107;26;27;58;59;90;91;122;123;12;13;44;45;76;77;108;109;28;29;60;61;92;93;124;125;14;15;46;47;78;79;110;111;30;31;62;63;94;95;126;127]
  axiomatized by perm_inv_level1E.

hoare invntt_avx_1 r:
  NTT_AVX.__invntt_level1 : perm_ntt perm_inv_level0 rp = r ==> perm_ntt perm_inv_level1 res = r_avx2_invntt NTT_Fq.zetas_inv r 1.
proof.
proc; inline *; wp; auto => /> &hr.
rewrite NTT_Fq.zetas_invE r_avx2_invntt_spec => />.
apply tP_red256 => i /=.
do 256!(try (move => Hi; case Hi => />); first by rewrite /perm_inv_level0 /perm_inv_level1 /shuffle1 //=).
qed.

lemma invntt_avx_1_pr r:
  phoare [NTT_AVX.__invntt_level1 : perm_ntt perm_inv_level0 rp = r ==> perm_ntt perm_inv_level1 res = r_avx2_invntt NTT_Fq.zetas_inv r 1] = 1%r.
proof. by conseq invntt_avx_1_ll (invntt_avx_1 r). qed.

op perm_inv_level2 : int list =
  [0;1;2;3;32;33;34;35;64;65;66;67;96;97;98;99;16;17;18;19;48;49;50;51;80;81;82;83;112;113;114;115;4;5;6;7;36;37;38;39;68;69;70;71;100;101;102;103;20;21;22;23;52;53;54;55;84;85;86;87;116;117;118;119;8;9;10;11;40;41;42;43;72;73;74;75;104;105;106;107;24;25;26;27;56;57;58;59;88;89;90;91;120;121;122;123;12;13;14;15;44;45;46;47;76;77;78;79;108;109;110;111;28;29;30;31;60;61;62;63;92;93;94;95;124;125;126;127]
  axiomatized by perm_inv_level2E.

hoare invntt_avx_2 r:
  NTT_AVX.__invntt_level2 : perm_ntt perm_inv_level1 rp = r ==> perm_ntt perm_inv_level2 res = r_avx2_invntt NTT_Fq.zetas_inv r 2.
proof.
proc; inline *; wp; auto => /> &hr.
rewrite NTT_Fq.zetas_invE r_avx2_invntt_spec => />.
apply tP_red256 => i /=.
do 256!(try (move => Hi; case Hi => />); first by rewrite /perm_inv_level1 /perm_inv_level2 /shuffle2 //=).
qed.

lemma invntt_avx_2_pr r:
  phoare [NTT_AVX.__invntt_level2 : perm_ntt perm_inv_level1 rp = r ==> perm_ntt perm_inv_level2 res = r_avx2_invntt NTT_Fq.zetas_inv r 2] = 1%r.
proof. by conseq invntt_avx_2_ll (invntt_avx_2 r). qed.

op perm_inv_level3 : int list =
  [0;1;2;3;4;5;6;7;32;33;34;35;36;37;38;39;64;65;66;67;68;69;70;71;96;97;98;99;100;101;102;103;16;17;18;19;20;21;22;23;48;49;50;51;52;53;54;55;80;81;82;83;84;85;86;87;112;113;114;115;116;117;118;119;8;9;10;11;12;13;14;15;40;41;42;43;44;45;46;47;72;73;74;75;76;77;78;79;104;105;106;107;108;109;110;111;24;25;26;27;28;29;30;31;56;57;58;59;60;61;62;63;88;89;90;91;92;93;94;95;120;121;122;123;124;125;126;127]
  axiomatized by perm_inv_level3E.

hoare invntt_avx_3 r:
  NTT_AVX.__invntt_level3 : perm_ntt perm_inv_level2 rp = r ==> perm_ntt perm_inv_level3 res = r_avx2_invntt NTT_Fq.zetas_inv r 3.
proof.
proc; inline *; wp; auto => /> &hr.
rewrite NTT_Fq.zetas_invE r_avx2_invntt_spec => />.
apply tP_red256 => i /=.
do 256!(try (move => Hi; case Hi => />); first by rewrite /perm_inv_level2 /perm_inv_level3 /shuffle4 //=).
qed.

lemma invntt_avx_3_pr r:
  phoare [NTT_AVX.__invntt_level3 : perm_ntt perm_inv_level2 rp = r ==> perm_ntt perm_inv_level3 res = r_avx2_invntt NTT_Fq.zetas_inv r 3] = 1%r.
proof. by conseq invntt_avx_3_ll (invntt_avx_3 r). qed.

op perm_inv_level4 : int list =
  [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127]
  axiomatized by perm_inv_level4E.

hoare invntt_avx_4 r:
  NTT_AVX.__invntt_level4 : perm_ntt perm_inv_level3 rp = r ==> perm_ntt perm_inv_level4 res = r_avx2_invntt NTT_Fq.zetas_inv r 4.
proof.
proc; inline *; wp; auto => /> &hr.
rewrite NTT_Fq.zetas_invE r_avx2_invntt_spec => />.
apply tP_red256 => i /=.
do 256!(try (move => Hi; case Hi => />); first by rewrite /perm_inv_level3 /perm_inv_level4 /shuffle8 //=).
qed.

lemma invntt_avx_4_pr r:
  phoare [NTT_AVX.__invntt_level4 : perm_ntt perm_inv_level3 rp = r ==> perm_ntt perm_inv_level4 res = r_avx2_invntt NTT_Fq.zetas_inv r 4] = 1%r.
proof. by conseq invntt_avx_4_ll (invntt_avx_4 r). qed.

hoare invntt_avx_5 r:
  NTT_AVX.__invntt_level5 : perm_ntt perm_inv_level4 rp = r ==> res = r_avx2_invntt NTT_Fq.zetas_inv r 5.
proof.
proc; inline *; wp; auto => /> &hr.
rewrite NTT_Fq.zetas_invE r_avx2_invntt_spec => />.
apply tP_red256 => i /=.
do 256!(try (move => Hi; case Hi => />); first by rewrite /perm_inv_level4 //=).
qed.

lemma invntt_avx_5_pr r:
  phoare [NTT_AVX.__invntt_level5 : perm_ntt perm_inv_level4 rp = r ==> res = r_avx2_invntt NTT_Fq.zetas_inv r 5] = 1%r.
proof. by conseq invntt_avx_5_ll (invntt_avx_5 r). qed.

hoare invntt_avx_6 r:
  NTT_AVX.___invntt_level6 : rp = r ==> res = r_avx2_invntt NTT_Fq.zetas_inv r 6.
proof.
proc; inline *; wp; auto => />. 
rewrite NTT_Fq.zetas_invE r_avx2_invntt_spec => />.
apply tP_red256 => i /=.
do 255!(move => Hi; case Hi => />).
qed.

lemma invntt_avx_6_pr r:
  phoare [NTT_AVX.___invntt_level6 : rp = r ==> res = r_avx2_invntt NTT_Fq.zetas_inv r 6] = 1%r.
proof. by conseq _invntt_avx_6_ll (invntt_avx_6 r). qed.

(** Main Theorem in this module: abstract coeff-based AVX implementation and original NTT specification are equivalent (inverse) **)
lemma invntt_avx2_equiv : 
     equiv [ NTT_AVX.invntt ~ NTT_avx2.invntt :
          perm_ntt perm_nttpack128 rp{1} = NTT_avx2.r{2} /\ NTT_avx2.zetas_inv{2} = NTT_Fq.zetas_inv
          ==> res{1} = res{2}].
proof.
proc*.
transitivity{1} { r <@ NTT_AVX.invntt0t6(r); }
  (rp{1}=r{2} ==> ={r})
  (perm_ntt perm_nttpack128 r{1} = NTT_avx2.r{2} /\ NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv  ==> r{1}=r{2}) => //.
  by move => /> &1 /#. 
call invntt0t6_invntt; first by auto.
inline NTT_AVX.invntt0t6 NTT_avx2.invntt.
(*level 0*)
rcondt{2} 2; auto => />.
seq 2 3 : (NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv /\ perm_ntt perm_inv_level0 rp0{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=1 ). 
ecall {1} (invntt_avx_0_pr (perm_ntt perm_nttpack128 r{1})).
 by auto => /> *. 
(*level 1*)
exlim NTT_avx2.r{2} => r0.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv /\ perm_ntt perm_inv_level1 rp1{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=2 ).
ecall {1} (invntt_avx_1_pr r0); auto.
(*level 2*)
exlim NTT_avx2.r{2} => r1.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv /\ perm_ntt perm_inv_level2 rp2{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=3 ).
call{1} (invntt_avx_2_pr r1); auto.
(*level 3*)
exlim NTT_avx2.r{2} => r2.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv /\ perm_ntt perm_inv_level3 rp3{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=4 ).
call{1} (invntt_avx_3_pr r2); auto.
(*level 4*)
exlim NTT_avx2.r{2} => r3.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv /\ perm_ntt perm_inv_level4 rp4{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=5 ).
call{1} (invntt_avx_4_pr r3); auto.
(*level 5*)
exlim NTT_avx2.r{2} => r4.
rcondt{2} 1; auto => />.
seq 1 2 : (NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv /\ rp5{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=6 ).
call{1} (invntt_avx_5_pr r4); auto.
(*level 6*)
exlim NTT_avx2.r{2} => r5.
rcondt{2} 1; auto => />.
inline{1} NTT_AVX.__invntt_level6.
seq 2 2 : (NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv /\ rp10{1}=NTT_avx2.r{2} /\ NTT_avx2.k{2}=7 ).
call{1} (invntt_avx_6_pr r5); auto.
(*exit*)
rcondf{2} 1; auto => /> &2.
rewrite r_avx2_invntt_post_spec /NTT_Fq.zetas_inv tP => />i Hi1 Hi2.
rewrite !initiE => />. 
rewrite mapiE // ZqField.mulrC; congr.
by rewrite -eq_incoeff /q //=.
qed.

lemma invntt_avx_equiv : 
     equiv [ NTT_AVX.invntt ~ NTT_AVX.invntt_bsrev :
          perm_ntt perm_nttpack128 rp{1} = r{2}
          ==> res{1} = res{2}].
proof.
proc*.
transitivity{1} { r <@ NTT_avx2.invntt(); }
  (perm_ntt perm_nttpack128 rp{1}=NTT_avx2.r{2} /\ NTT_avx2.zetas_inv{2}=NTT_Fq.zetas_inv ==> ={r})
  (NTT_avx2.r{1} = r{2} /\ NTT_avx2.zetas_inv{1}=NTT_Fq.zetas_inv ==> r{1}=r0{2}) => //.
move => /> &1 /#. 
call invntt_avx2_equiv; first by auto.
inline NTT_AVX.invntt_bsrev; wp; sp => />. symmetry.
call avx2_invntt; auto. qed.

hoare invntt_bsrev_h _r: 
   NTT_AVX.invntt_bsrev:
    r = _r ==> res = invntt _r.
proof.
proc.
ecall (bsrev_invntt_spec NTT_vars.r).
wp; skip => /> rr.
by apply imp_invntt_spec.
qed.


hoare invntt_avx_h _r:
 NTT_AVX.invntt : perm_ntt perm_nttpack128 rp = _r ==> res = invntt _r.
proof.
bypr => // &m <-. clear _r. 
have <-: Pr[NTT_AVX.invntt_bsrev(perm_ntt perm_nttpack128 arg{m}) @ &m : res <> invntt (perm_ntt perm_nttpack128 arg{m})] = 0%r.
 byphoare (_:r=perm_ntt perm_nttpack128 arg{m} ==> _) => //. hoare => />.
 conseq (invntt_bsrev_h (perm_ntt perm_nttpack128 arg{m})) => />.
byequiv => //.
conseq invntt_avx_equiv => />. qed.

lemma invntt_avx_ll: islossless  NTT_AVX.invntt by islossless.

phoare invntt_avx_spec _r:
 [ NTT_AVX.invntt : perm_ntt perm_nttpack128 rp = _r ==>  res = invntt _r ] = 1%r.
proof. conseq invntt_avx_ll (invntt_avx_h _r) => />. qed.
