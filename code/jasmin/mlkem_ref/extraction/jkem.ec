require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.


require import Array4 Array5 Array24 Array25 Array32 Array33 Array34 Array64
               Array128 Array168 Array256 Array768 Array960 Array1088
               Array2304.
require import WArray20 WArray32 WArray33 WArray34 WArray40 WArray64
               WArray128 WArray168 WArray192 WArray200 WArray256 WArray512
               WArray960 WArray1088 WArray1536 WArray4608.

abbrev jzetas_inv = Array128.of_list witness [W16.of_int 1701;
W16.of_int 1807; W16.of_int 1460; W16.of_int 2371; W16.of_int 2338;
W16.of_int 2333; W16.of_int 308; W16.of_int 108; W16.of_int 2851;
W16.of_int 870; W16.of_int 854; W16.of_int 1510; W16.of_int 2535;
W16.of_int 1278; W16.of_int 1530; W16.of_int 1185; W16.of_int 1659;
W16.of_int 1187; W16.of_int 3109; W16.of_int 874; W16.of_int 1335;
W16.of_int 2111; W16.of_int 136; W16.of_int 1215; W16.of_int 2945;
W16.of_int 1465; W16.of_int 1285; W16.of_int 2007; W16.of_int 2719;
W16.of_int 2726; W16.of_int 2232; W16.of_int 2512; W16.of_int 75;
W16.of_int 156; W16.of_int 3000; W16.of_int 2911; W16.of_int 2980;
W16.of_int 872; W16.of_int 2685; W16.of_int 1590; W16.of_int 2210;
W16.of_int 602; W16.of_int 1846; W16.of_int 777; W16.of_int 147;
W16.of_int 2170; W16.of_int 2551; W16.of_int 246; W16.of_int 1676;
W16.of_int 1755; W16.of_int 460; W16.of_int 291; W16.of_int 235;
W16.of_int 3152; W16.of_int 2742; W16.of_int 2907; W16.of_int 3224;
W16.of_int 1779; W16.of_int 2458; W16.of_int 1251; W16.of_int 2486;
W16.of_int 2774; W16.of_int 2899; W16.of_int 1103; W16.of_int 1275;
W16.of_int 2652; W16.of_int 1065; W16.of_int 2881; W16.of_int 725;
W16.of_int 1508; W16.of_int 2368; W16.of_int 398; W16.of_int 951;
W16.of_int 247; W16.of_int 1421; W16.of_int 3222; W16.of_int 2499;
W16.of_int 271; W16.of_int 90; W16.of_int 853; W16.of_int 1860;
W16.of_int 3203; W16.of_int 1162; W16.of_int 1618; W16.of_int 666;
W16.of_int 320; W16.of_int 8; W16.of_int 2813; W16.of_int 1544;
W16.of_int 282; W16.of_int 1838; W16.of_int 1293; W16.of_int 2314;
W16.of_int 552; W16.of_int 2677; W16.of_int 2106; W16.of_int 1571;
W16.of_int 205; W16.of_int 2918; W16.of_int 1542; W16.of_int 2721;
W16.of_int 2597; W16.of_int 2312; W16.of_int 681; W16.of_int 130;
W16.of_int 1602; W16.of_int 1871; W16.of_int 829; W16.of_int 2946;
W16.of_int 3065; W16.of_int 1325; W16.of_int 2756; W16.of_int 1861;
W16.of_int 1474; W16.of_int 1202; W16.of_int 2367; W16.of_int 3147;
W16.of_int 1752; W16.of_int 2707; W16.of_int 171; W16.of_int 3127;
W16.of_int 3042; W16.of_int 1907; W16.of_int 1836; W16.of_int 1517;
W16.of_int 359; W16.of_int 758; W16.of_int 1441].


abbrev jzetas = Array128.of_list witness [W16.of_int 2285; W16.of_int 2571;
W16.of_int 2970; W16.of_int 1812; W16.of_int 1493; W16.of_int 1422;
W16.of_int 287; W16.of_int 202; W16.of_int 3158; W16.of_int 622;
W16.of_int 1577; W16.of_int 182; W16.of_int 962; W16.of_int 2127;
W16.of_int 1855; W16.of_int 1468; W16.of_int 573; W16.of_int 2004;
W16.of_int 264; W16.of_int 383; W16.of_int 2500; W16.of_int 1458;
W16.of_int 1727; W16.of_int 3199; W16.of_int 2648; W16.of_int 1017;
W16.of_int 732; W16.of_int 608; W16.of_int 1787; W16.of_int 411;
W16.of_int 3124; W16.of_int 1758; W16.of_int 1223; W16.of_int 652;
W16.of_int 2777; W16.of_int 1015; W16.of_int 2036; W16.of_int 1491;
W16.of_int 3047; W16.of_int 1785; W16.of_int 516; W16.of_int 3321;
W16.of_int 3009; W16.of_int 2663; W16.of_int 1711; W16.of_int 2167;
W16.of_int 126; W16.of_int 1469; W16.of_int 2476; W16.of_int 3239;
W16.of_int 3058; W16.of_int 830; W16.of_int 107; W16.of_int 1908;
W16.of_int 3082; W16.of_int 2378; W16.of_int 2931; W16.of_int 961;
W16.of_int 1821; W16.of_int 2604; W16.of_int 448; W16.of_int 2264;
W16.of_int 677; W16.of_int 2054; W16.of_int 2226; W16.of_int 430;
W16.of_int 555; W16.of_int 843; W16.of_int 2078; W16.of_int 871;
W16.of_int 1550; W16.of_int 105; W16.of_int 422; W16.of_int 587;
W16.of_int 177; W16.of_int 3094; W16.of_int 3038; W16.of_int 2869;
W16.of_int 1574; W16.of_int 1653; W16.of_int 3083; W16.of_int 778;
W16.of_int 1159; W16.of_int 3182; W16.of_int 2552; W16.of_int 1483;
W16.of_int 2727; W16.of_int 1119; W16.of_int 1739; W16.of_int 644;
W16.of_int 2457; W16.of_int 349; W16.of_int 418; W16.of_int 329;
W16.of_int 3173; W16.of_int 3254; W16.of_int 817; W16.of_int 1097;
W16.of_int 603; W16.of_int 610; W16.of_int 1322; W16.of_int 2044;
W16.of_int 1864; W16.of_int 384; W16.of_int 2114; W16.of_int 3193;
W16.of_int 1218; W16.of_int 1994; W16.of_int 2455; W16.of_int 220;
W16.of_int 2142; W16.of_int 1670; W16.of_int 2144; W16.of_int 1799;
W16.of_int 2051; W16.of_int 794; W16.of_int 1819; W16.of_int 2475;
W16.of_int 2459; W16.of_int 478; W16.of_int 3221; W16.of_int 3021;
W16.of_int 996; W16.of_int 991; W16.of_int 958; W16.of_int 1869;
W16.of_int 1522; W16.of_int 1628].


abbrev kECCAK1600_RC = Array24.of_list witness [W64.of_int 1;
W64.of_int 32898; W64.of_int (-9223372036854742902);
W64.of_int (-9223372034707259392); W64.of_int 32907; W64.of_int 2147483649;
W64.of_int (-9223372034707259263); W64.of_int (-9223372036854743031);
W64.of_int 138; W64.of_int 136; W64.of_int 2147516425; W64.of_int 2147483658;
W64.of_int 2147516555; W64.of_int (-9223372036854775669);
W64.of_int (-9223372036854742903); W64.of_int (-9223372036854743037);
W64.of_int (-9223372036854743038); W64.of_int (-9223372036854775680);
W64.of_int 32778; W64.of_int (-9223372034707292150);
W64.of_int (-9223372034707259263); W64.of_int (-9223372036854742912);
W64.of_int 2147483649; W64.of_int (-9223372034707259384)].


module type Syscall_t = {
  proc randombytes_32(_:W8.t Array32.t) : W8.t Array32.t
  proc randombytes_64(_:W8.t Array64.t) : W8.t Array64.t
}.

module Syscall : Syscall_t = {
  proc randombytes_32(a:W8.t Array32.t) : W8.t Array32.t = {
    a <$ dmap WArray32.darray
         (fun a => Array32.init (fun i => WArray32.get8 a i));
    return a;
  }
  
  proc randombytes_64(a:W8.t Array64.t) : W8.t Array64.t = {
    a <$ dmap WArray64.darray
         (fun a => Array64.init (fun i => WArray64.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc __fqmul (a:W16.t, b:W16.t) : W16.t = {
    
    var r:W16.t;
    var ad:W32.t;
    var bd:W32.t;
    var c:W32.t;
    var u:W32.t;
    var t:W32.t;
    
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    u <- (c * (W32.of_int (62209 `<<` 16)));
    u <- (u `|>>` (W8.of_int 16));
    t <- (u * (W32.of_int (- 3329)));
    t <- (t + c);
    t <- (t `|>>` (W8.of_int 16));
    r <- (truncateu16 t);
    return (r);
  }
  
  proc __barrett_reduce (a:W16.t) : W16.t = {
    
    var r:W16.t;
    var t:W32.t;
    
    t <- (sigextu32 a);
    t <- (t * (W32.of_int 20159));
    t <- (t `|>>` (W8.of_int 26));
    t <- (t * (W32.of_int 3329));
    r <- (truncateu16 t);
    r <- a;
    r <- (r - (truncateu16 t));
    return (r);
  }
  
  proc keccakf1600_index (x:int, y:int) : int = {
    
    var r:int;
    
    r <- ((x %% 5) + (5 * (y %% 5)));
    return (r);
  }
  
  proc keccakf1600_rho_offsets (i:int) : int = {
    var aux: int;
    
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while (t < 24) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- t + 1;
    }
    return (r);
  }
  
  proc keccakf1600_rhotates (x:int, y:int) : int = {
    
    var r:int;
    var i:int;
    
    i <@ keccakf1600_index (x, y);
    r <@ keccakf1600_rho_offsets (i);
    return (r);
  }
  
  proc keccakf1600_theta_sum (a:W64.t Array25.t) : W64.t Array5.t = {
    var aux: int;
    
    var c:W64.t Array5.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while (x < 5) {
      c.[x] <- a.[(x + 0)];
      x <- x + 1;
    }
    y <- 1;
    while (y < 5) {
      x <- 0;
      while (x < 5) {
        c.[x] <- (c.[x] `^` a.[(x + (y * 5))]);
        x <- x + 1;
      }
      y <- y + 1;
    }
    return (c);
  }
  
  proc keccakf1600_theta_rol (c:W64.t Array5.t) : W64.t Array5.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux: int;
    var aux_2: W64.t;
    
    var d:W64.t Array5.t;
    var x:int;
    var  _0:bool;
    var  _1:bool;
    d <- witness;
    x <- 0;
    while (x < 5) {
      d.[x] <- c.[((x + 1) %% 5)];
      (aux_1, aux_0, aux_2) <- ROL_64 d.[x] (W8.of_int 1);
       _0 <- aux_1;
       _1 <- aux_0;
      d.[x] <- aux_2;
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- x + 1;
    }
    return (d);
  }
  
  proc keccakf1600_rol_sum (a:W64.t Array25.t, d:W64.t Array5.t, y:int) : 
  W64.t Array5.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux: int;
    var aux_2: W64.t;
    
    var b:W64.t Array5.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    var  _0:bool;
    var  _1:bool;
    b <- witness;
    x <- 0;
    while (x < 5) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      r <@ keccakf1600_rhotates (x_, y_);
      b.[x] <- a.[(x_ + (y_ * 5))];
      b.[x] <- (b.[x] `^` d.[x_]);
      if ((r <> 0)) {
        (aux_1, aux_0, aux_2) <- ROL_64 b.[x] (W8.of_int r);
         _0 <- aux_1;
         _1 <- aux_0;
        b.[x] <- aux_2;
      } else {
        
      }
      x <- x + 1;
    }
    return (b);
  }
  
  proc keccakf1600_set_row (e:W64.t Array25.t, b:W64.t Array5.t, y:int,
                            s_rc:W64.t) : W64.t Array25.t = {
    var aux: int;
    
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    
    x <- 0;
    while (x < 5) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <- b.[x1];
      t <- (invw t);
      t <- (t `&` b.[x2]);
      t <- (t `^` b.[x]);
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` s_rc);
      } else {
        
      }
      e.[(x + (y * 5))] <- t;
      x <- x + 1;
    }
    return (e);
  }
  
  proc keccakf1600_round (e:W64.t Array25.t, a:W64.t Array25.t, rc:W64.t) : 
  W64.t Array25.t = {
    var aux: int;
    
    var s_rc:W64.t;
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;
    var y:int;
    var b:W64.t Array5.t;
    b <- witness;
    c <- witness;
    d <- witness;
    s_rc <- rc;
    c <@ keccakf1600_theta_sum (a);
    d <@ keccakf1600_theta_rol (c);
    y <- 0;
    while (y < 5) {
      b <@ keccakf1600_rol_sum (a, d, y);
      e <@ keccakf1600_set_row (e, b, y, s_rc);
      y <- y + 1;
    }
    return (e);
  }
  
  proc __keccakf1600 (a:W64.t Array25.t) : W64.t Array25.t = {
    
    var rC:W64.t Array24.t;
    var s_e:W64.t Array25.t;
    var e:W64.t Array25.t;
    var c:W64.t;
    var rc:W64.t;
    rC <- witness;
    e <- witness;
    s_e <- witness;
    rC <- kECCAK1600_RC;
    e <- s_e;
    c <- (W64.of_int 0);
    
    while ((c \ult (W64.of_int (24 - 1)))) {
      rc <- rC.[(W64.to_uint c)];
      e <@ keccakf1600_round (e, a, rc);
      rc <- rC.[((W64.to_uint c) + 1)];
      a <@ keccakf1600_round (a, e, rc);
      c <- (c + (W64.of_int 2));
    }
    return (a);
  }
  
  proc _keccakf1600 (a:W64.t Array25.t) : W64.t Array25.t = {
    
    
    
    a <@ __keccakf1600 (a);
    return (a);
  }
  
  proc _keccakf1600_ (a:W64.t Array25.t) : W64.t Array25.t = {
    
    
    
    a <- a;
    a <@ _keccakf1600 (a);
    a <- a;
    return (a);
  }
  
  proc __st0 (state:W64.t Array25.t) : W64.t Array25.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 25) {
      state.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (state);
  }
  
  proc __add_full_block (state:W64.t Array25.t, in_0:W64.t, inlen:W64.t,
                         r8:W64.t) : W64.t Array25.t * W64.t * W64.t = {
    
    var r64:W64.t;
    var i:W64.t;
    var t:W64.t;
    
    r64 <- r8;
    r64 <- (r64 `>>` (W8.of_int 3));
    i <- (W64.of_int 0);
    
    while ((i \ult r64)) {
      t <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))));
      state.[(W64.to_uint i)] <- (state.[(W64.to_uint i)] `^` t);
      i <- (i + (W64.of_int 1));
    }
    in_0 <- (in_0 + r8);
    inlen <- (inlen - r8);
    return (state, in_0, inlen);
  }
  
  proc __add_final_block (state:W64.t Array25.t, in_0:W64.t, inlen:W64.t,
                          trail_byte:W8.t, r8:W64.t) : W64.t Array25.t = {
    
    var inlen8:W64.t;
    var i:W64.t;
    var t:W64.t;
    var c:W8.t;
    
    inlen8 <- inlen;
    inlen8 <- (inlen8 `>>` (W8.of_int 3));
    i <- (W64.of_int 0);
    
    while ((i \ult inlen8)) {
      t <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))));
      state.[(W64.to_uint i)] <- (state.[(W64.to_uint i)] `^` t);
      i <- (i + (W64.of_int 1));
    }
    i <- (i `<<` (W8.of_int 3));
    
    while ((i \ult inlen)) {
      c <- (loadW8 Glob.mem (W64.to_uint (in_0 + i)));
      state <-
      Array25.init
      (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (W64.to_uint i) ((
      (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (W64.to_uint i)) `^` c))));
      i <- (i + (W64.of_int 1));
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (W64.to_uint i) ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (W64.to_uint i)) `^` trail_byte))));
    i <- r8;
    i <- (i - (W64.of_int 1));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (W64.to_uint i) ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (W64.to_uint i)) `^` (W8.of_int 128)))));
    return (state);
  }
  
  proc _shake256_128_33 (out:W8.t Array128.t, in_0:W8.t Array33.t) : 
  W8.t Array128.t = {
    var aux: int;
    
    var sout:W8.t Array128.t;
    var state:W64.t Array25.t;
    var i:int;
    var c:W8.t;
    sout <- witness;
    state <- witness;
    sout <- out;
    state <@ __st0 (state);
    i <- 0;
    while (i < 33) {
      c <- in_0.[i];
      state <-
      Array25.init
      (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) i ((
      (get8 (WArray200.init64 (fun i_0 => state.[i_0])) i) `^` c))));
      i <- i + 1;
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 33 ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) 33) `^` (W8.of_int 31)))));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (136 - 1) ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (136 - 1)) `^` (W8.of_int 128)))));
    state <@ _keccakf1600_ (state);
    out <- sout;
    i <- 0;
    while (i < 128) {
      c <- (get8 (WArray200.init64 (fun i_0 => state.[i_0])) i);
      out.[i] <- c;
      i <- i + 1;
    }
    return (out);
  }
  
  proc _shake256_1120_32 (out:W64.t, in0:W64.t, in1:W64.t) : unit = {
    var aux: int;
    
    var s_out:W64.t;
    var s_in1:W64.t;
    var state:W64.t Array25.t;
    var i:int;
    var t64:W64.t;
    var r8:W64.t;
    var ilen:W64.t;
    var in_0:W64.t;
    var s_in:W64.t;
    var s_ilen:W64.t;
    var s_r8:W64.t;
    var t8:W8.t;
    state <- witness;
    s_out <- out;
    s_in1 <- in1;
    state <@ __st0 (state);
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (loadW64 Glob.mem (W64.to_uint (in0 + (W64.of_int (i * 8)))));
      state.[i] <- (state.[i] `^` t64);
      i <- i + 1;
    }
    aux <- (136 %/ 8);
    i <- (32 %/ 8);
    while (i < aux) {
      t64 <-
      (loadW64 Glob.mem (W64.to_uint (in1 + (W64.of_int ((i - (32 %/ 8)) * 8)))));
      state.[i] <- (state.[i] `^` t64);
      i <- i + 1;
    }
    state <@ _keccakf1600_ (state);
    r8 <- (W64.of_int 136);
    ilen <- (W64.of_int (((3 * 320) + 128) - (136 - 32)));
    in_0 <- s_in1;
    in_0 <- (in_0 + (W64.of_int (136 - 32)));
    
    while ((r8 \ule ilen)) {
      (state, in_0, ilen) <@ __add_full_block (state, in_0, ilen, r8);
      s_in <- in_0;
      s_ilen <- ilen;
      s_r8 <- r8;
      state <@ _keccakf1600_ (state);
      in_0 <- s_in;
      ilen <- s_ilen;
      r8 <- s_r8;
    }
    t8 <- (W8.of_int 31);
    state <@ __add_final_block (state, in_0, ilen, t8, r8);
    state <@ _keccakf1600_ (state);
    out <- s_out;
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- state.[i];
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (8 * i)))) (t64);
      i <- i + 1;
    }
    return ();
  }
  
  proc _sha3512_32 (out:W8.t Array64.t, in_0:W8.t Array32.t) : W8.t Array64.t = {
    var aux: int;
    
    var s_out:W8.t Array64.t;
    var state:W64.t Array25.t;
    var i:int;
    var c:W8.t;
    s_out <- witness;
    state <- witness;
    s_out <- out;
    state <@ __st0 (state);
    i <- 0;
    while (i < 32) {
      c <- in_0.[i];
      state <-
      Array25.init
      (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) i ((
      (get8 (WArray200.init64 (fun i_0 => state.[i_0])) i) `^` c))));
      i <- i + 1;
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 32 ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) 32) `^` (W8.of_int 6)))));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (72 - 1) ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (72 - 1)) `^` (W8.of_int 128)))));
    state <@ _keccakf1600_ (state);
    out <- s_out;
    i <- 0;
    while (i < 64) {
      c <- (get8 (WArray200.init64 (fun i_0 => state.[i_0])) i);
      out.[i] <- c;
      i <- i + 1;
    }
    return (out);
  }
  
  proc _shake128_absorb34 (state:W64.t Array25.t, in_0:W8.t Array34.t) : 
  W64.t Array25.t = {
    var aux: int;
    
    var i:int;
    var c:W8.t;
    
    state <@ __st0 (state);
    i <- 0;
    while (i < 34) {
      c <- in_0.[i];
      state <-
      Array25.init
      (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) i ((
      (get8 (WArray200.init64 (fun i_0 => state.[i_0])) i) `^` c))));
      i <- i + 1;
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 34 ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) 34) `^` (W8.of_int 31)))));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (168 - 1) ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (168 - 1)) `^` (W8.of_int 128)))));
    return (state);
  }
  
  proc _shake128_squeezeblock (state:W64.t Array25.t, out:W8.t Array168.t) : 
  W64.t Array25.t * W8.t Array168.t = {
    var aux: int;
    
    var s_out:W8.t Array168.t;
    var i:int;
    var c:W8.t;
    s_out <- witness;
    s_out <- out;
    state <@ _keccakf1600_ (state);
    out <- s_out;
    i <- 0;
    while (i < 168) {
      c <- (get8 (WArray200.init64 (fun i_0 => state.[i_0])) i);
      out.[i] <- c;
      i <- i + 1;
    }
    return (state, out);
  }
  
  proc _isha3_256 (out:W8.t Array32.t, in_0:W64.t, inlen:W64.t) : W8.t Array32.t = {
    var aux: int;
    
    var s_out:W8.t Array32.t;
    var state:W64.t Array25.t;
    var r8:W64.t;
    var ilen:W64.t;
    var s_in:W64.t;
    var s_ilen:W64.t;
    var s_r8:W64.t;
    var t8:W8.t;
    var i:int;
    var t64:W64.t;
    s_out <- witness;
    state <- witness;
    s_out <- out;
    state <@ __st0 (state);
    r8 <- (W64.of_int 136);
    ilen <- inlen;
    
    while ((r8 \ule ilen)) {
      (state, in_0, ilen) <@ __add_full_block (state, in_0, ilen, r8);
      s_in <- in_0;
      s_ilen <- ilen;
      s_r8 <- r8;
      state <@ _keccakf1600_ (state);
      in_0 <- s_in;
      ilen <- s_ilen;
      r8 <- s_r8;
    }
    t8 <- (W8.of_int 6);
    state <@ __add_final_block (state, in_0, ilen, t8, r8);
    state <@ _keccakf1600_ (state);
    out <- s_out;
    i <- 0;
    while (i < 4) {
      t64 <- state.[i];
      out <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => out.[i_0])) i (t64)));
      i <- i + 1;
    }
    return (out);
  }
  
  proc _sha3_512_64 (out:W8.t Array64.t, in_0:W8.t Array64.t) : W8.t Array64.t = {
    var aux: int;
    
    var state:W64.t Array25.t;
    var i:int;
    var t64:W64.t;
    var out_s:W8.t Array64.t;
    out_s <- witness;
    state <- witness;
    state <@ __st0 (state);
    i <- 0;
    while (i < 8) {
      t64 <- (get64 (WArray64.init8 (fun i_0 => in_0.[i_0])) i);
      state.[i] <- (state.[i] `^` t64);
      i <- i + 1;
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 64 ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) 64) `^` (W8.of_int 6)))));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (72 - 1) ((
    (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (72 - 1)) `^` (W8.of_int 128)))));
    out_s <- out;
    state <@ _keccakf1600_ (state);
    out <- out_s;
    i <- 0;
    while (i < 8) {
      t64 <- state.[i];
      out <-
      Array64.init
      (WArray64.get8 (WArray64.set64 (WArray64.init8 (fun i_0 => out.[i_0])) i (t64)));
      i <- i + 1;
    }
    return (out);
  }
  
  proc _poly_add2 (rp:W16.t Array256.t, bp:W16.t Array256.t) : W16.t Array256.t = {
    
    var i:W64.t;
    var a:W16.t;
    var b:W16.t;
    var r:W16.t;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 256))) {
      a <- rp.[(W64.to_uint i)];
      b <- bp.[(W64.to_uint i)];
      r <- (a + b);
      rp.[(W64.to_uint i)] <- r;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _poly_csubq (rp:W16.t Array256.t) : W16.t Array256.t = {
    
    var i:W64.t;
    var t:W16.t;
    var b:W16.t;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 256))) {
      t <- rp.[(W64.to_uint i)];
      t <- (t - (W16.of_int 3329));
      b <- t;
      b <- (b `|>>` (W8.of_int 15));
      b <- (b `&` (W16.of_int 3329));
      t <- (t + b);
      rp.[(W64.to_uint i)] <- t;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _poly_basemul (rp:W16.t Array256.t, ap:W16.t Array256.t,
                      bp:W16.t Array256.t) : W16.t Array256.t = {
    
    var srp:W16.t Array256.t;
    var i:W64.t;
    var zetasp:W16.t Array64.t;
    var zetasctr:W64.t;
    var zeta_0:W16.t;
    var a0:W16.t;
    var b0:W16.t;
    var a1:W16.t;
    var b1:W16.t;
    var r0:W16.t;
    var t:W16.t;
    var r1:W16.t;
    srp <- witness;
    zetasp <- witness;
    srp <- rp;
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int (256 - 3)))) {
      zetasp <- (Array64.init (fun i_0 => jzetas.[64 + i_0]));
      zetasctr <- i;
      zetasctr <- (zetasctr `>>` (W8.of_int 2));
      zeta_0 <- zetasp.[(W64.to_uint zetasctr)];
      a0 <- ap.[(W64.to_uint i)];
      b0 <- bp.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      a1 <- ap.[(W64.to_uint i)];
      b1 <- bp.[(W64.to_uint i)];
      i <- (i - (W64.of_int 1));
      r0 <@ __fqmul (a1, b1);
      r0 <@ __fqmul (r0, zeta_0);
      t <@ __fqmul (a0, b0);
      r0 <- (r0 + t);
      r1 <@ __fqmul (a0, b1);
      t <@ __fqmul (a1, b0);
      r1 <- (r1 + t);
      rp <- srp;
      rp.[(W64.to_uint i)] <- r0;
      i <- (i + (W64.of_int 1));
      rp.[(W64.to_uint i)] <- r1;
      srp <- rp;
      zeta_0 <- (- zeta_0);
      i <- (i + (W64.of_int 1));
      a0 <- ap.[(W64.to_uint i)];
      b0 <- bp.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      a1 <- ap.[(W64.to_uint i)];
      b1 <- bp.[(W64.to_uint i)];
      i <- (i - (W64.of_int 1));
      r0 <@ __fqmul (a1, b1);
      r0 <@ __fqmul (r0, zeta_0);
      t <@ __fqmul (a0, b0);
      r0 <- (r0 + t);
      r1 <@ __fqmul (a0, b1);
      t <@ __fqmul (a1, b0);
      r1 <- (r1 + t);
      rp <- srp;
      rp.[(W64.to_uint i)] <- r0;
      i <- (i + (W64.of_int 1));
      rp.[(W64.to_uint i)] <- r1;
      srp <- rp;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc __poly_reduce (rp:W16.t Array256.t) : W16.t Array256.t = {
    
    var j:W64.t;
    var t:W16.t;
    
    j <- (W64.of_int 0);
    
    while ((j \ult (W64.of_int 256))) {
      t <- rp.[(W64.to_uint j)];
      t <@ __barrett_reduce (t);
      rp.[(W64.to_uint j)] <- t;
      j <- (j + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _poly_compress (rp:W64.t, a:W16.t Array256.t) : W16.t Array256.t = {
    
    var i:W64.t;
    var d0:W32.t;
    var d1:W32.t;
    
    a <@ _poly_csubq (a);
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 128))) {
      d0 <- (zeroextu32 a.[(W64.to_uint ((W64.of_int 2) * i))]);
      d1 <-
      (zeroextu32 a.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))]);
      d0 <- (d0 `<<` (W8.of_int 4));
      d0 <- (d0 + (W32.of_int 1665));
      d0 <- (d0 * (W32.of_int 80635));
      d0 <- (d0 `>>` (W8.of_int 28));
      d0 <- (d0 `&` (W32.of_int 15));
      d1 <- (d1 `<<` (W8.of_int 4));
      d1 <- (d1 + (W32.of_int 1665));
      d1 <- (d1 * (W32.of_int 80635));
      d1 <- (d1 `>>` (W8.of_int 28));
      d1 <- (d1 `&` (W32.of_int 15));
      d1 <- (d1 `<<` (W8.of_int 4));
      d0 <- (d0 `|` d1);
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + i)) ((truncateu8 d0));
      i <- (i + (W64.of_int 1));
    }
    return (a);
  }
  
  proc _i_poly_compress (rp:W8.t Array128.t, a:W16.t Array256.t) : W8.t Array128.t *
                                                                   W16.t Array256.t = {
    
    var i:W64.t;
    var d0:W32.t;
    var d1:W32.t;
    
    a <@ _poly_csubq (a);
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 128))) {
      d0 <- (zeroextu32 a.[(W64.to_uint ((W64.of_int 2) * i))]);
      d1 <-
      (zeroextu32 a.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))]);
      d0 <- (d0 `<<` (W8.of_int 4));
      d0 <- (d0 + (W32.of_int 1665));
      d0 <- (d0 * (W32.of_int 80635));
      d0 <- (d0 `>>` (W8.of_int 28));
      d0 <- (d0 `&` (W32.of_int 15));
      d1 <- (d1 `<<` (W8.of_int 4));
      d1 <- (d1 + (W32.of_int 1665));
      d1 <- (d1 * (W32.of_int 80635));
      d1 <- (d1 `>>` (W8.of_int 28));
      d1 <- (d1 `&` (W32.of_int 15));
      d1 <- (d1 `<<` (W8.of_int 4));
      d0 <- (d0 `|` d1);
      rp.[(W64.to_uint i)] <- (truncateu8 d0);
      i <- (i + (W64.of_int 1));
    }
    return (rp, a);
  }
  
  proc _poly_decompress (rp:W16.t Array256.t, ap:W64.t) : W16.t Array256.t = {
    
    var i:W64.t;
    var t:W8.t;
    var d0:W16.t;
    var d1:W16.t;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 128))) {
      t <- (loadW8 Glob.mem (W64.to_uint (ap + i)));
      d0 <- (zeroextu16 t);
      d1 <- (zeroextu16 t);
      d0 <- (d0 `&` (W16.of_int 15));
      d1 <- (d1 `>>` (W8.of_int 4));
      d0 <- (d0 * (W16.of_int 3329));
      d1 <- (d1 * (W16.of_int 3329));
      d0 <- (d0 + (W16.of_int 8));
      d1 <- (d1 + (W16.of_int 8));
      d0 <- (d0 `>>` (W8.of_int 4));
      d1 <- (d1 `>>` (W8.of_int 4));
      rp.[(W64.to_uint ((W64.of_int 2) * i))] <- d0;
      rp.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))] <- d1;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _poly_frombytes (rp:W16.t Array256.t, ap:W64.t) : W16.t Array256.t = {
    var aux: int;
    
    var i:int;
    var c0:W8.t;
    var c1:W8.t;
    var c2:W8.t;
    var d0:W16.t;
    var t:W16.t;
    var d1:W16.t;
    
    aux <- (256 %/ 2);
    i <- 0;
    while (i < aux) {
      c0 <- (loadW8 Glob.mem (W64.to_uint (ap + (W64.of_int (3 * i)))));
      c1 <-
      (loadW8 Glob.mem (W64.to_uint (ap + (W64.of_int ((3 * i) + 1)))));
      c2 <-
      (loadW8 Glob.mem (W64.to_uint (ap + (W64.of_int ((3 * i) + 2)))));
      d0 <- (zeroextu16 c0);
      t <- (zeroextu16 c1);
      t <- (t `&` (W16.of_int 15));
      t <- (t `<<` (W8.of_int 8));
      d0 <- (d0 `|` t);
      d1 <- (zeroextu16 c2);
      d1 <- (d1 `<<` (W8.of_int 4));
      t <- (zeroextu16 c1);
      t <- (t `>>` (W8.of_int 4));
      d1 <- (d1 `|` t);
      rp.[(2 * i)] <- d0;
      rp.[((2 * i) + 1)] <- d1;
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_frommont (rp:W16.t Array256.t) : W16.t Array256.t = {
    
    var dmont:W16.t;
    var i:W64.t;
    var r:W16.t;
    
    dmont <- (W16.of_int 1353);
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 256))) {
      r <- rp.[(W64.to_uint i)];
      r <@ __fqmul (r, dmont);
      rp.[(W64.to_uint i)] <- r;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _i_poly_frommsg (rp:W16.t Array256.t, ap:W8.t Array32.t) : W16.t Array256.t = {
    var aux: int;
    
    var i:int;
    var c:W8.t;
    var t:W16.t;
    
    i <- 0;
    while (i < 32) {
      c <- ap.[i];
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[(8 * i)] <- t;
      c <- (c `>>` (W8.of_int 1));
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[((8 * i) + 1)] <- t;
      c <- (c `>>` (W8.of_int 1));
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[((8 * i) + 2)] <- t;
      c <- (c `>>` (W8.of_int 1));
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[((8 * i) + 3)] <- t;
      c <- (c `>>` (W8.of_int 1));
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[((8 * i) + 4)] <- t;
      c <- (c `>>` (W8.of_int 1));
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[((8 * i) + 5)] <- t;
      c <- (c `>>` (W8.of_int 1));
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[((8 * i) + 6)] <- t;
      c <- (c `>>` (W8.of_int 1));
      t <- (zeroextu16 c);
      t <- (t `&` (W16.of_int 1));
      t <- (t * (W16.of_int ((3329 + 1) %/ 2)));
      rp.[((8 * i) + 7)] <- t;
      c <- (c `>>` (W8.of_int 1));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_getnoise (rp:W16.t Array256.t, seed:W8.t Array32.t, nonce:W8.t) : 
  W16.t Array256.t = {
    var aux: int;
    
    var srp:W16.t Array256.t;
    var k:int;
    var c:W8.t;
    var extseed:W8.t Array33.t;
    var buf:W8.t Array128.t;
    var i:W64.t;
    var a:W8.t;
    var b:W8.t;
    var t:W16.t;
    buf <- witness;
    extseed <- witness;
    srp <- witness;
    srp <- rp;
    k <- 0;
    while (k < 32) {
      c <- seed.[k];
      extseed.[k] <- c;
      k <- k + 1;
    }
    extseed.[32] <- nonce;
    buf <@ _shake256_128_33 (buf, extseed);
    rp <- srp;
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
      rp.[(W64.to_uint ((W64.of_int 2) * i))] <- t;
      a <- c;
      a <- (a `>>` (W8.of_int 4));
      a <- (a `&` (W8.of_int 3));
      b <- (c `>>` (W8.of_int 6));
      b <- (b `&` (W8.of_int 3));
      a <- (a - b);
      t <- (sigextu16 a);
      rp.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))] <- t;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _poly_invntt (rp:W16.t Array256.t) : W16.t Array256.t = {
    
    var zetasp:W16.t Array128.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W16.t;
    var j:W64.t;
    var cmp:W64.t;
    var t:W16.t;
    var offset:W64.t;
    var s:W16.t;
    var m:W16.t;
    zetasp <- witness;
    zetasp <- jzetas_inv;
    zetasctr <- (W64.of_int 0);
    len <- (W64.of_int 2);
    
    while ((len \ule (W64.of_int 128))) {
      start <- (W64.of_int 0);
      
      while ((start \ult (W64.of_int 256))) {
        zeta_0 <- zetasp.[(W64.to_uint zetasctr)];
        zetasctr <- (zetasctr + (W64.of_int 1));
        j <- start;
        cmp <- start;
        cmp <- (cmp + len);
        
        while ((j \ult cmp)) {
          t <- rp.[(W64.to_uint j)];
          offset <- j;
          offset <- (offset + len);
          s <- rp.[(W64.to_uint offset)];
          m <- s;
          m <- (m + t);
          m <@ __barrett_reduce (m);
          rp.[(W64.to_uint j)] <- m;
          t <- (t - s);
          t <@ __fqmul (t, zeta_0);
          rp.[(W64.to_uint offset)] <- t;
          j <- (j + (W64.of_int 1));
        }
        start <- j;
        start <- (start + len);
      }
      len <- (len `<<` (W8.of_int 1));
    }
    zeta_0 <- zetasp.[127];
    j <- (W64.of_int 0);
    
    while ((j \ult (W64.of_int 256))) {
      t <- rp.[(W64.to_uint j)];
      t <@ __fqmul (t, zeta_0);
      rp.[(W64.to_uint j)] <- t;
      j <- (j + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _poly_ntt (rp:W16.t Array256.t) : W16.t Array256.t = {
    
    var zetasp:W16.t Array128.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W16.t;
    var j:W64.t;
    var cmp:W64.t;
    var s:W16.t;
    var m:W16.t;
    var offset:W64.t;
    var t:W16.t;
    zetasp <- witness;
    zetasp <- jzetas;
    zetasctr <- (W64.of_int 0);
    len <- (W64.of_int 128);
    
    while (((W64.of_int 2) \ule len)) {
      start <- (W64.of_int 0);
      
      while ((start \ult (W64.of_int 256))) {
        zetasctr <- (zetasctr + (W64.of_int 1));
        zeta_0 <- zetasp.[(W64.to_uint zetasctr)];
        j <- start;
        cmp <- start;
        cmp <- (cmp + len);
        
        while ((j \ult cmp)) {
          s <- rp.[(W64.to_uint j)];
          m <- s;
          offset <- j;
          offset <- (offset + len);
          t <- rp.[(W64.to_uint offset)];
          t <@ __fqmul (t, zeta_0);
          m <- (m - t);
          t <- (t + s);
          rp.[(W64.to_uint offset)] <- m;
          rp.[(W64.to_uint j)] <- t;
          j <- (j + (W64.of_int 1));
        }
        start <- j;
        start <- (start + len);
      }
      len <- (len `>>` (W8.of_int 1));
    }
    rp <@ __poly_reduce (rp);
    return (rp);
  }
  
  proc _poly_sub (rp:W16.t Array256.t, ap:W16.t Array256.t,
                  bp:W16.t Array256.t) : W16.t Array256.t = {
    
    var i:W64.t;
    var a:W16.t;
    var b:W16.t;
    var r:W16.t;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 256))) {
      a <- ap.[(W64.to_uint i)];
      b <- bp.[(W64.to_uint i)];
      r <- (a - b);
      rp.[(W64.to_uint i)] <- r;
      i <- (i + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc _poly_tobytes (rp:W64.t, a:W16.t Array256.t) : W16.t Array256.t = {
    
    var i:W64.t;
    var j:W64.t;
    var t0:W16.t;
    var t1:W16.t;
    var d:W16.t;
    
    a <@ _poly_csubq (a);
    i <- (W64.of_int 0);
    j <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 256))) {
      t0 <- a.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      t1 <- a.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      d <- t0;
      d <- (d `&` (W16.of_int 255));
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 d));
      j <- (j + (W64.of_int 1));
      t0 <- (t0 `>>` (W8.of_int 8));
      d <- t1;
      d <- (d `&` (W16.of_int 15));
      d <- (d `<<` (W8.of_int 4));
      d <- (d `|` t0);
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 d));
      j <- (j + (W64.of_int 1));
      t1 <- (t1 `>>` (W8.of_int 4));
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 t1));
      j <- (j + (W64.of_int 1));
    }
    return (a);
  }
  
  proc _i_poly_tomsg (rp:W8.t Array32.t, a:W16.t Array256.t) : W8.t Array32.t *
                                                               W16.t Array256.t = {
    var aux: int;
    
    var r:W8.t;
    var j:int;
    var i:int;
    var t:W16.t;
    var d:W32.t;
    
    a <@ _poly_csubq (a);
    i <- 0;
    while (i < 32) {
      r <- (W8.of_int 0);
      j <- 0;
      while (j < 8) {
        t <- a.[((8 * i) + j)];
        d <- (zeroextu32 t);
        d <- (d `<<` (W8.of_int 1));
        d <- (d + (W32.of_int 1665));
        d <- (d * (W32.of_int 80635));
        d <- (d `>>` (W8.of_int 28));
        d <- (d `&` (W32.of_int 1));
        d <- (d `<<` (W8.of_int j));
        r <- (r `|` (truncateu8 d));
        j <- j + 1;
      }
      rp.[i] <- r;
      i <- i + 1;
    }
    return (rp, a);
  }
  
  proc __polyvec_add2 (r:W16.t Array768.t, b:W16.t Array768.t) : W16.t Array768.t = {
    var aux: W16.t Array256.t;
    
    
    
    aux <@ _poly_add2 ((Array256.init (fun i => r.[0 + i])),
    (Array256.init (fun i => b.[0 + i])));
    r <- Array768.init
         (fun i => if 0 <= i < 0 + 256 then aux.[i-0] else r.[i]);
    aux <@ _poly_add2 ((Array256.init (fun i => r.[256 + i])),
    (Array256.init (fun i => b.[256 + i])));
    r <- Array768.init
         (fun i => if 256 <= i < 256 + 256 then aux.[i-256] else r.[i]);
    aux <@ _poly_add2 ((Array256.init (fun i => r.[(2 * 256) + i])),
    (Array256.init (fun i => b.[(2 * 256) + i])));
    r <- Array768.init
         (fun i => if (2 * 256) <= i < (2 * 256) + 256 then aux.[i-(2 * 256)]
         else r.[i]);
    return (r);
  }
  
  proc __polyvec_csubq (r:W16.t Array768.t) : W16.t Array768.t = {
    var aux: W16.t Array256.t;
    
    
    
    aux <@ _poly_csubq ((Array256.init (fun i => r.[0 + i])));
    r <- Array768.init
         (fun i => if 0 <= i < 0 + 256 then aux.[i-0] else r.[i]);
    aux <@ _poly_csubq ((Array256.init (fun i => r.[256 + i])));
    r <- Array768.init
         (fun i => if 256 <= i < 256 + 256 then aux.[i-256] else r.[i]);
    aux <@ _poly_csubq ((Array256.init (fun i => r.[(2 * 256) + i])));
    r <- Array768.init
         (fun i => if (2 * 256) <= i < (2 * 256) + 256 then aux.[i-(2 * 256)]
         else r.[i]);
    return (r);
  }
  
  proc __polyvec_compress (rp:W64.t, a:W16.t Array768.t) : unit = {
    var aux: int;
    
    var i:W64.t;
    var j:W64.t;
    var aa:W16.t Array768.t;
    var k:int;
    var t:W64.t Array4.t;
    var c:W16.t;
    var b:W16.t;
    aa <- witness;
    t <- witness;
    i <- (W64.of_int 0);
    j <- (W64.of_int 0);
    aa <@ __polyvec_csubq (a);
    
    while ((i \ult (W64.of_int ((3 * 256) - 3)))) {
      k <- 0;
      while (k < 4) {
        t.[k] <- (zeroextu64 aa.[(W64.to_uint i)]);
        i <- (i + (W64.of_int 1));
        t.[k] <- (t.[k] `<<` (W8.of_int 10));
        t.[k] <- (t.[k] + (W64.of_int 1665));
        t.[k] <- (t.[k] * (W64.of_int 1290167));
        t.[k] <- (t.[k] `>>` (W8.of_int 32));
        t.[k] <- (t.[k] `&` (W64.of_int 1023));
        k <- k + 1;
      }
      c <- (truncateu16 t.[0]);
      c <- (c `&` (W16.of_int 255));
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 c));
      j <- (j + (W64.of_int 1));
      b <- (truncateu16 t.[0]);
      b <- (b `>>` (W8.of_int 8));
      c <- (truncateu16 t.[1]);
      c <- (c `<<` (W8.of_int 2));
      c <- (c `|` b);
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 c));
      j <- (j + (W64.of_int 1));
      b <- (truncateu16 t.[1]);
      b <- (b `>>` (W8.of_int 6));
      c <- (truncateu16 t.[2]);
      c <- (c `<<` (W8.of_int 4));
      c <- (c `|` b);
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 c));
      j <- (j + (W64.of_int 1));
      b <- (truncateu16 t.[2]);
      b <- (b `>>` (W8.of_int 4));
      c <- (truncateu16 t.[3]);
      c <- (c `<<` (W8.of_int 6));
      c <- (c `|` b);
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 c));
      j <- (j + (W64.of_int 1));
      t.[3] <- (t.[3] `>>` (W8.of_int 2));
      Glob.mem <-
      storeW8 Glob.mem (W64.to_uint (rp + j)) ((truncateu8 t.[3]));
      j <- (j + (W64.of_int 1));
    }
    return ();
  }
  
  proc __i_polyvec_compress (rp:W8.t Array960.t, a:W16.t Array768.t) : 
  W8.t Array960.t = {
    var aux: int;
    
    var i:W64.t;
    var j:W64.t;
    var aa:W16.t Array768.t;
    var k:int;
    var t:W64.t Array4.t;
    var c:W16.t;
    var b:W16.t;
    aa <- witness;
    t <- witness;
    i <- (W64.of_int 0);
    j <- (W64.of_int 0);
    aa <@ __polyvec_csubq (a);
    
    while ((i \ult (W64.of_int ((3 * 256) - 3)))) {
      k <- 0;
      while (k < 4) {
        t.[k] <- (zeroextu64 aa.[(W64.to_uint i)]);
        i <- (i + (W64.of_int 1));
        t.[k] <- (t.[k] `<<` (W8.of_int 10));
        t.[k] <- (t.[k] + (W64.of_int 1665));
        t.[k] <- (t.[k] * (W64.of_int 1290167));
        t.[k] <- (t.[k] `>>` (W8.of_int 32));
        t.[k] <- (t.[k] `&` (W64.of_int 1023));
        k <- k + 1;
      }
      c <- (truncateu16 t.[0]);
      c <- (c `&` (W16.of_int 255));
      rp.[(W64.to_uint j)] <- (truncateu8 c);
      j <- (j + (W64.of_int 1));
      b <- (truncateu16 t.[0]);
      b <- (b `>>` (W8.of_int 8));
      c <- (truncateu16 t.[1]);
      c <- (c `<<` (W8.of_int 2));
      c <- (c `|` b);
      rp.[(W64.to_uint j)] <- (truncateu8 c);
      j <- (j + (W64.of_int 1));
      b <- (truncateu16 t.[1]);
      b <- (b `>>` (W8.of_int 6));
      c <- (truncateu16 t.[2]);
      c <- (c `<<` (W8.of_int 4));
      c <- (c `|` b);
      rp.[(W64.to_uint j)] <- (truncateu8 c);
      j <- (j + (W64.of_int 1));
      b <- (truncateu16 t.[2]);
      b <- (b `>>` (W8.of_int 4));
      c <- (truncateu16 t.[3]);
      c <- (c `<<` (W8.of_int 6));
      c <- (c `|` b);
      rp.[(W64.to_uint j)] <- (truncateu8 c);
      j <- (j + (W64.of_int 1));
      t.[3] <- (t.[3] `>>` (W8.of_int 2));
      rp.[(W64.to_uint j)] <- (truncateu8 t.[3]);
      j <- (j + (W64.of_int 1));
    }
    return (rp);
  }
  
  proc __polyvec_decompress (ap:W64.t) : W16.t Array768.t = {
    var aux: int;
    
    var r:W16.t Array768.t;
    var i:W64.t;
    var j:W64.t;
    var k:int;
    var t:W32.t Array5.t;
    var d:W32.t;
    r <- witness;
    t <- witness;
    i <- (W64.of_int 0);
    j <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int ((3 * 256) - 3)))) {
      k <- 0;
      while (k < 5) {
        t.[k] <- (zeroextu32 (loadW8 Glob.mem (W64.to_uint (ap + j))));
        j <- (j + (W64.of_int 1));
        k <- k + 1;
      }
      d <- t.[1];
      t.[1] <- (t.[1] `>>` (W8.of_int 2));
      d <- (d `&` (W32.of_int 3));
      d <- (d `<<` (W8.of_int 8));
      t.[0] <- (t.[0] `|` d);
      d <- t.[2];
      t.[2] <- (t.[2] `>>` (W8.of_int 4));
      d <- (d `&` (W32.of_int 15));
      d <- (d `<<` (W8.of_int 6));
      t.[1] <- (t.[1] `|` d);
      d <- t.[3];
      t.[3] <- (t.[3] `>>` (W8.of_int 6));
      d <- (d `&` (W32.of_int 63));
      d <- (d `<<` (W8.of_int 4));
      t.[2] <- (t.[2] `|` d);
      d <- t.[4];
      d <- (d `<<` (W8.of_int 2));
      t.[3] <- (t.[3] `|` d);
      k <- 0;
      while (k < 4) {
        t.[k] <- (t.[k] * (W32.of_int 3329));
        t.[k] <- (t.[k] + (W32.of_int 512));
        t.[k] <- (t.[k] `>>` (W8.of_int 10));
        r.[(W64.to_uint i)] <- (truncateu16 t.[k]);
        i <- (i + (W64.of_int 1));
        k <- k + 1;
      }
    }
    return (r);
  }
  
  proc __polyvec_frombytes (ap:W64.t) : W16.t Array768.t = {
    var aux: W16.t Array256.t;
    
    var r:W16.t Array768.t;
    var pp:W64.t;
    r <- witness;
    pp <- ap;
    aux <@ _poly_frombytes ((Array256.init (fun i => r.[0 + i])), pp);
    r <- Array768.init
         (fun i => if 0 <= i < 0 + 256 then aux.[i-0] else r.[i]);
    pp <- (pp + (W64.of_int 384));
    aux <@ _poly_frombytes ((Array256.init (fun i => r.[256 + i])), pp);
    r <- Array768.init
         (fun i => if 256 <= i < 256 + 256 then aux.[i-256] else r.[i]);
    pp <- (pp + (W64.of_int 384));
    aux <@ _poly_frombytes ((Array256.init (fun i => r.[(2 * 256) + i])),
    pp);
    r <- Array768.init
         (fun i => if (2 * 256) <= i < (2 * 256) + 256 then aux.[i-(2 * 256)]
         else r.[i]);
    return (r);
  }
  
  proc __polyvec_invntt (r:W16.t Array768.t) : W16.t Array768.t = {
    var aux: W16.t Array256.t;
    
    
    
    aux <@ _poly_invntt ((Array256.init (fun i => r.[0 + i])));
    r <- Array768.init
         (fun i => if 0 <= i < 0 + 256 then aux.[i-0] else r.[i]);
    aux <@ _poly_invntt ((Array256.init (fun i => r.[256 + i])));
    r <- Array768.init
         (fun i => if 256 <= i < 256 + 256 then aux.[i-256] else r.[i]);
    aux <@ _poly_invntt ((Array256.init (fun i => r.[(2 * 256) + i])));
    r <- Array768.init
         (fun i => if (2 * 256) <= i < (2 * 256) + 256 then aux.[i-(2 * 256)]
         else r.[i]);
    return (r);
  }
  
  proc __polyvec_ntt (r:W16.t Array768.t) : W16.t Array768.t = {
    var aux: W16.t Array256.t;
    
    
    
    aux <@ _poly_ntt ((Array256.init (fun i => r.[0 + i])));
    r <- Array768.init
         (fun i => if 0 <= i < 0 + 256 then aux.[i-0] else r.[i]);
    aux <@ _poly_ntt ((Array256.init (fun i => r.[256 + i])));
    r <- Array768.init
         (fun i => if 256 <= i < 256 + 256 then aux.[i-256] else r.[i]);
    aux <@ _poly_ntt ((Array256.init (fun i => r.[(2 * 256) + i])));
    r <- Array768.init
         (fun i => if (2 * 256) <= i < (2 * 256) + 256 then aux.[i-(2 * 256)]
         else r.[i]);
    return (r);
  }
  
  proc __polyvec_pointwise_acc (a:W16.t Array768.t, b:W16.t Array768.t) : 
  W16.t Array256.t = {
    
    var r:W16.t Array256.t;
    var t:W16.t Array256.t;
    r <- witness;
    t <- witness;
    r <@ _poly_basemul (r, (Array256.init (fun i => a.[0 + i])),
    (Array256.init (fun i => b.[0 + i])));
    t <@ _poly_basemul (t, (Array256.init (fun i => a.[256 + i])),
    (Array256.init (fun i => b.[256 + i])));
    r <@ _poly_add2 (r, t);
    t <@ _poly_basemul (t, (Array256.init (fun i => a.[(2 * 256) + i])),
    (Array256.init (fun i => b.[(2 * 256) + i])));
    r <@ _poly_add2 (r, t);
    r <@ __poly_reduce (r);
    return (r);
  }
  
  proc __polyvec_reduce (r:W16.t Array768.t) : W16.t Array768.t = {
    var aux: W16.t Array256.t;
    
    
    
    aux <@ __poly_reduce ((Array256.init (fun i => r.[0 + i])));
    r <- Array768.init
         (fun i => if 0 <= i < 0 + 256 then aux.[i-0] else r.[i]);
    aux <@ __poly_reduce ((Array256.init (fun i => r.[256 + i])));
    r <- Array768.init
         (fun i => if 256 <= i < 256 + 256 then aux.[i-256] else r.[i]);
    aux <@ __poly_reduce ((Array256.init (fun i => r.[(2 * 256) + i])));
    r <- Array768.init
         (fun i => if (2 * 256) <= i < (2 * 256) + 256 then aux.[i-(2 * 256)]
         else r.[i]);
    return (r);
  }
  
  proc __polyvec_tobytes (rp:W64.t, a:W16.t Array768.t) : unit = {
    var aux: W16.t Array256.t;
    
    var pp:W64.t;
    
    pp <- rp;
    aux <@ _poly_tobytes (pp, (Array256.init (fun i => a.[0 + i])));
    a <- Array768.init
         (fun i => if 0 <= i < 0 + 256 then aux.[i-0] else a.[i]);
    pp <- (pp + (W64.of_int 384));
    aux <@ _poly_tobytes (pp, (Array256.init (fun i => a.[256 + i])));
    a <- Array768.init
         (fun i => if 256 <= i < 256 + 256 then aux.[i-256] else a.[i]);
    pp <- (pp + (W64.of_int 384));
    aux <@ _poly_tobytes (pp, (Array256.init (fun i => a.[(2 * 256) + i])));
    a <- Array768.init
         (fun i => if (2 * 256) <= i < (2 * 256) + 256 then aux.[i-(2 * 256)]
         else a.[i]);
    return ();
  }
  
  proc __rej_uniform (rp:W16.t Array256.t, offset:W64.t, buf:W8.t Array168.t) : 
  W64.t * W16.t Array256.t = {
    
    var ctr:W64.t;
    var pos:W64.t;
    var val1:W16.t;
    var t:W16.t;
    var val2:W16.t;
    
    ctr <- offset;
    pos <- (W64.of_int 0);
    
    while ((pos \ult (W64.of_int (168 - 2)))) {
      if ((ctr \ult (W64.of_int 256))) {
        val1 <- (zeroextu16 buf.[(W64.to_uint pos)]);
        t <- (zeroextu16 buf.[(W64.to_uint (pos + (W64.of_int 1)))]);
        val2 <- t;
        val2 <- (val2 `>>` (W8.of_int 4));
        t <- (t `&` (W16.of_int 15));
        t <- (t `<<` (W8.of_int 8));
        val1 <- (val1 `|` t);
        t <- (zeroextu16 buf.[(W64.to_uint (pos + (W64.of_int 2)))]);
        t <- (t `<<` (W8.of_int 4));
        val2 <- (val2 `|` t);
        pos <- (pos + (W64.of_int 3));
        if ((val1 \ult (W16.of_int 3329))) {
          rp.[(W64.to_uint ctr)] <- val1;
          ctr <- (ctr + (W64.of_int 1));
        } else {
          
        }
        if ((val2 \ult (W16.of_int 3329))) {
          if ((ctr \ult (W64.of_int 256))) {
            rp.[(W64.to_uint ctr)] <- val2;
            ctr <- (ctr + (W64.of_int 1));
          } else {
            
          }
        } else {
          
        }
      } else {
        pos <- (W64.of_int 168);
      }
    }
    return (ctr, rp);
  }
  
  proc __gen_matrix (seed:W8.t Array32.t, transposed:W64.t) : W16.t Array2304.t = {
    var aux: int;
    
    var r:W16.t Array2304.t;
    var stransposed:W64.t;
    var j:int;
    var c:W8.t;
    var extseed:W8.t Array34.t;
    var i:int;
    var state:W64.t Array25.t;
    var ctr:W64.t;
    var sctr:W64.t;
    var buf:W8.t Array168.t;
    var poly:W16.t Array256.t;
    var k:W64.t;
    var rij:W16.t Array256.t;
    var t:W16.t;
    buf <- witness;
    extseed <- witness;
    poly <- witness;
    r <- witness;
    rij <- witness;
    state <- witness;
    stransposed <- transposed;
    j <- 0;
    while (j < 32) {
      c <- seed.[j];
      extseed.[j] <- c;
      j <- j + 1;
    }
    i <- 0;
    while (i < 3) {
      j <- 0;
      while (j < 3) {
        transposed <- stransposed;
        if ((transposed = (W64.of_int 0))) {
          extseed.[32] <- (W8.of_int j);
          extseed.[(32 + 1)] <- (W8.of_int i);
        } else {
          extseed.[32] <- (W8.of_int i);
          extseed.[(32 + 1)] <- (W8.of_int j);
        }
        state <@ _shake128_absorb34 (state, extseed);
        ctr <- (W64.of_int 0);
        
        while ((ctr \ult (W64.of_int 256))) {
          sctr <- ctr;
          (state, buf) <@ _shake128_squeezeblock (state, buf);
          ctr <- sctr;
          (ctr, poly) <@ __rej_uniform (poly, ctr, buf);
        }
        k <- (W64.of_int 0);
        rij <-
        (Array256.init (fun i_0 => r.[((i * (3 * 256)) + (j * 256)) + i_0]));
        
        while ((k \ult (W64.of_int 256))) {
          t <- poly.[(W64.to_uint k)];
          rij.[(W64.to_uint k)] <- t;
          k <- (k + (W64.of_int 1));
        }
        r <- Array2304.init
             (fun i_0 => if ((i * (3 * 256)) + (j * 256)) <= i_0 < ((i * (3 * 256)) + (j * 256)) + 256
             then rij.[i_0-((i * (3 * 256)) + (j * 256))] else r.[i_0]);
        j <- j + 1;
      }
      i <- i + 1;
    }
    return (r);
  }
  
  proc __indcpa_keypair (pkp:W64.t, skp:W64.t, randomnessp:W8.t Array32.t) : unit = {
    var aux: int;
    var aux_0: W16.t Array256.t;
    
    var spkp:W64.t;
    var sskp:W64.t;
    var i:int;
    var t64:W64.t;
    var inbuf:W8.t Array32.t;
    var buf:W8.t Array64.t;
    var publicseed:W8.t Array32.t;
    var noiseseed:W8.t Array32.t;
    var zero:W64.t;
    var a:W16.t Array2304.t;
    var nonce:W8.t;
    var skpv:W16.t Array768.t;
    var e:W16.t Array768.t;
    var pkpv:W16.t Array768.t;
    a <- witness;
    buf <- witness;
    e <- witness;
    inbuf <- witness;
    noiseseed <- witness;
    pkpv <- witness;
    publicseed <- witness;
    skpv <- witness;
    spkp <- pkp;
    sskp <- skp;
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => randomnessp.[i_0])) i);
      inbuf <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => inbuf.[i_0])) i (t64)));
      i <- i + 1;
    }
    buf <@ _sha3512_32 (buf, inbuf);
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray64.init8 (fun i_0 => buf.[i_0])) i);
      publicseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => publicseed.[i_0])) i (t64)));
      t64 <- (get64 (WArray64.init8 (fun i_0 => buf.[i_0])) (i + (32 %/ 8)));
      noiseseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => noiseseed.[i_0])) i (t64)));
      i <- i + 1;
    }
    zero <- (W64.of_int 0);
    a <@ __gen_matrix (publicseed, zero);
    nonce <- (W8.of_int 0);
    aux_0 <@ _poly_getnoise ((Array256.init (fun i_0 => skpv.[0 + i_0])),
    noiseseed, nonce);
    skpv <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_0.[i_0-0]
            else skpv.[i_0]);
    nonce <- (W8.of_int 1);
    aux_0 <@ _poly_getnoise ((Array256.init (fun i_0 => skpv.[256 + i_0])),
    noiseseed, nonce);
    skpv <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_0.[i_0-256]
            else skpv.[i_0]);
    nonce <- (W8.of_int 2);
    aux_0 <@ _poly_getnoise ((Array256.init (fun i_0 => skpv.[(2 * 256) + i_0])),
    noiseseed, nonce);
    skpv <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux_0.[i_0-(2 * 256)] else skpv.[i_0]);
    nonce <- (W8.of_int 3);
    aux_0 <@ _poly_getnoise ((Array256.init (fun i_0 => e.[0 + i_0])),
    noiseseed, nonce);
    e <- Array768.init
         (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_0.[i_0-0] else e.[i_0]);
    nonce <- (W8.of_int 4);
    aux_0 <@ _poly_getnoise ((Array256.init (fun i_0 => e.[256 + i_0])),
    noiseseed, nonce);
    e <- Array768.init
         (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_0.[i_0-256]
         else e.[i_0]);
    nonce <- (W8.of_int 5);
    aux_0 <@ _poly_getnoise ((Array256.init (fun i_0 => e.[(2 * 256) + i_0])),
    noiseseed, nonce);
    e <- Array768.init
         (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
         then aux_0.[i_0-(2 * 256)] else e.[i_0]);
    skpv <@ __polyvec_ntt (skpv);
    e <@ __polyvec_ntt (e);
    aux_0 <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => a.[0 + i_0])),
    skpv);
    pkpv <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_0.[i_0-0]
            else pkpv.[i_0]);
    aux_0 <@ _poly_frommont ((Array256.init (fun i_0 => pkpv.[0 + i_0])));
    pkpv <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_0.[i_0-0]
            else pkpv.[i_0]);
    aux_0 <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => a.[(3 * 256) + i_0])),
    skpv);
    pkpv <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_0.[i_0-256]
            else pkpv.[i_0]);
    aux_0 <@ _poly_frommont ((Array256.init (fun i_0 => pkpv.[256 + i_0])));
    pkpv <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_0.[i_0-256]
            else pkpv.[i_0]);
    aux_0 <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => a.[(2 * (3 * 256)) + i_0])),
    skpv);
    pkpv <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux_0.[i_0-(2 * 256)] else pkpv.[i_0]);
    aux_0 <@ _poly_frommont ((Array256.init (fun i_0 => pkpv.[(2 * 256) + i_0])));
    pkpv <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux_0.[i_0-(2 * 256)] else pkpv.[i_0]);
    pkpv <@ __polyvec_add2 (pkpv, e);
    pkpv <@ __polyvec_reduce (pkpv);
    pkp <- spkp;
    skp <- sskp;
    __polyvec_tobytes (skp, skpv);
    __polyvec_tobytes (pkp, pkpv);
    pkp <- (pkp + (W64.of_int (3 * 384)));
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => publicseed.[i_0])) i);
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (pkp + (W64.of_int 0))) (t64);
      pkp <- (pkp + (W64.of_int 8));
      i <- i + 1;
    }
    return ();
  }
  
  proc __indcpa_enc (sctp:W64.t, msgp:W8.t Array32.t, pkp:W64.t,
                     noiseseed:W8.t Array32.t) : unit = {
    var aux: W16.t Array256.t;
    
    var s_noiseseed:W8.t Array32.t;
    var pkpv:W16.t Array768.t;
    var i:W64.t;
    var t64:W64.t;
    var publicseed:W8.t Array32.t;
    var k:W16.t Array256.t;
    var aat:W16.t Array2304.t;
    var nonce:W8.t;
    var sp_0:W16.t Array768.t;
    var ep:W16.t Array768.t;
    var epp:W16.t Array256.t;
    var bp:W16.t Array768.t;
    var v:W16.t Array256.t;
    var ctp:W64.t;
    aat <- witness;
    bp <- witness;
    ep <- witness;
    epp <- witness;
    k <- witness;
    pkpv <- witness;
    publicseed <- witness;
    s_noiseseed <- witness;
    sp_0 <- witness;
    v <- witness;
    s_noiseseed <- noiseseed;
    pkpv <@ __polyvec_frombytes (pkp);
    i <- (W64.of_int 0);
    pkp <- (pkp + (W64.of_int (3 * 384)));
    
    while ((i \ult (W64.of_int (32 %/ 8)))) {
      t64 <- (loadW64 Glob.mem (W64.to_uint (pkp + (W64.of_int 0))));
      publicseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64_direct (WArray32.init8 (fun i_0 => publicseed.[i_0])) (8 * (W64.to_uint i)) (t64)));
      pkp <- (pkp + (W64.of_int 8));
      i <- (i + (W64.of_int 1));
    }
    k <@ _i_poly_frommsg (k, msgp);
    aat <@ __gen_matrix (publicseed, (W64.of_int 1));
    nonce <- (W8.of_int 0);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => sp_0.[0 + i_0])),
    s_noiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0]
            else sp_0.[i_0]);
    nonce <- (W8.of_int 1);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => sp_0.[256 + i_0])),
    s_noiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux.[i_0-256]
            else sp_0.[i_0]);
    nonce <- (W8.of_int 2);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => sp_0.[(2 * 256) + i_0])),
    s_noiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux.[i_0-(2 * 256)] else sp_0.[i_0]);
    nonce <- (W8.of_int 3);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => ep.[0 + i_0])),
    s_noiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else ep.[i_0]);
    nonce <- (W8.of_int 4);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => ep.[256 + i_0])),
    s_noiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if 256 <= i_0 < 256 + 256 then aux.[i_0-256]
          else ep.[i_0]);
    nonce <- (W8.of_int 5);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => ep.[(2 * 256) + i_0])),
    s_noiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
          then aux.[i_0-(2 * 256)] else ep.[i_0]);
    nonce <- (W8.of_int 6);
    epp <@ _poly_getnoise (epp, s_noiseseed, nonce);
    sp_0 <@ __polyvec_ntt (sp_0);
    aux <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => aat.[0 + i_0])),
    sp_0);
    bp <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else bp.[i_0]);
    aux <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => aat.[(3 * 256) + i_0])),
    sp_0);
    bp <- Array768.init
          (fun i_0 => if 256 <= i_0 < 256 + 256 then aux.[i_0-256]
          else bp.[i_0]);
    aux <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => aat.[(2 * (3 * 256)) + i_0])),
    sp_0);
    bp <- Array768.init
          (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
          then aux.[i_0-(2 * 256)] else bp.[i_0]);
    v <@ __polyvec_pointwise_acc (pkpv, sp_0);
    bp <@ __polyvec_invntt (bp);
    v <@ _poly_invntt (v);
    bp <@ __polyvec_add2 (bp, ep);
    v <@ _poly_add2 (v, epp);
    v <@ _poly_add2 (v, k);
    bp <@ __polyvec_reduce (bp);
    v <@ __poly_reduce (v);
    ctp <- sctp;
    __polyvec_compress (ctp, bp);
    ctp <- (ctp + (W64.of_int (3 * 320)));
    v <@ _poly_compress (ctp, v);
    return ();
  }
  
  proc __iindcpa_enc (ctp:W8.t Array1088.t, msgp:W8.t Array32.t, pkp:W64.t,
                      noiseseed:W8.t Array32.t) : W8.t Array1088.t = {
    var aux_1: W8.t Array128.t;
    var aux_0: W8.t Array960.t;
    var aux: W16.t Array256.t;
    
    var s_noiseseed:W8.t Array32.t;
    var sctp:W8.t Array1088.t;
    var pkpv:W16.t Array768.t;
    var i:W64.t;
    var t64:W64.t;
    var publicseed:W8.t Array32.t;
    var k:W16.t Array256.t;
    var aat:W16.t Array2304.t;
    var nonce:W8.t;
    var sp_0:W16.t Array768.t;
    var ep:W16.t Array768.t;
    var epp:W16.t Array256.t;
    var bp:W16.t Array768.t;
    var v:W16.t Array256.t;
    aat <- witness;
    bp <- witness;
    ep <- witness;
    epp <- witness;
    k <- witness;
    pkpv <- witness;
    publicseed <- witness;
    s_noiseseed <- witness;
    sctp <- witness;
    sp_0 <- witness;
    v <- witness;
    s_noiseseed <- noiseseed;
    sctp <- ctp;
    pkpv <@ __polyvec_frombytes (pkp);
    i <- (W64.of_int 0);
    pkp <- (pkp + (W64.of_int (3 * 384)));
    
    while ((i \ult (W64.of_int (32 %/ 8)))) {
      t64 <- (loadW64 Glob.mem (W64.to_uint (pkp + (W64.of_int 0))));
      publicseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64_direct (WArray32.init8 (fun i_0 => publicseed.[i_0])) (8 * (W64.to_uint i)) (t64)));
      pkp <- (pkp + (W64.of_int 8));
      i <- (i + (W64.of_int 1));
    }
    k <@ _i_poly_frommsg (k, msgp);
    aat <@ __gen_matrix (publicseed, (W64.of_int 1));
    nonce <- (W8.of_int 0);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => sp_0.[0 + i_0])),
    s_noiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0]
            else sp_0.[i_0]);
    nonce <- (W8.of_int 1);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => sp_0.[256 + i_0])),
    s_noiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux.[i_0-256]
            else sp_0.[i_0]);
    nonce <- (W8.of_int 2);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => sp_0.[(2 * 256) + i_0])),
    s_noiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux.[i_0-(2 * 256)] else sp_0.[i_0]);
    nonce <- (W8.of_int 3);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => ep.[0 + i_0])),
    s_noiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else ep.[i_0]);
    nonce <- (W8.of_int 4);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => ep.[256 + i_0])),
    s_noiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if 256 <= i_0 < 256 + 256 then aux.[i_0-256]
          else ep.[i_0]);
    nonce <- (W8.of_int 5);
    aux <@ _poly_getnoise ((Array256.init (fun i_0 => ep.[(2 * 256) + i_0])),
    s_noiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
          then aux.[i_0-(2 * 256)] else ep.[i_0]);
    nonce <- (W8.of_int 6);
    epp <@ _poly_getnoise (epp, s_noiseseed, nonce);
    sp_0 <@ __polyvec_ntt (sp_0);
    aux <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => aat.[0 + i_0])),
    sp_0);
    bp <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else bp.[i_0]);
    aux <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => aat.[(3 * 256) + i_0])),
    sp_0);
    bp <- Array768.init
          (fun i_0 => if 256 <= i_0 < 256 + 256 then aux.[i_0-256]
          else bp.[i_0]);
    aux <@ __polyvec_pointwise_acc ((Array768.init (fun i_0 => aat.[(2 * (3 * 256)) + i_0])),
    sp_0);
    bp <- Array768.init
          (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
          then aux.[i_0-(2 * 256)] else bp.[i_0]);
    v <@ __polyvec_pointwise_acc (pkpv, sp_0);
    bp <@ __polyvec_invntt (bp);
    v <@ _poly_invntt (v);
    bp <@ __polyvec_add2 (bp, ep);
    v <@ _poly_add2 (v, epp);
    v <@ _poly_add2 (v, k);
    bp <@ __polyvec_reduce (bp);
    v <@ __poly_reduce (v);
    ctp <- sctp;
    aux_0 <@ __i_polyvec_compress ((Array960.init (fun i_0 => ctp.[0 + i_0])),
    bp);
    ctp <- Array1088.init
           (fun i_0 => if 0 <= i_0 < 0 + 960 then aux_0.[i_0-0]
           else ctp.[i_0]);
    (aux_1,
    aux) <@ _i_poly_compress ((Array128.init (fun i_0 => ctp.[(3 * 320) + i_0])),
    v);
    ctp <- Array1088.init
           (fun i_0 => if (3 * 320) <= i_0 < (3 * 320) + 128
           then aux_1.[i_0-(3 * 320)] else ctp.[i_0]);
    v <- aux;
    return (ctp);
  }
  
  proc __indcpa_dec (msgp:W8.t Array32.t, ctp:W64.t, skp:W64.t) : W8.t Array32.t = {
    
    var bp:W16.t Array768.t;
    var v:W16.t Array256.t;
    var skpv:W16.t Array768.t;
    var t:W16.t Array256.t;
    var mp:W16.t Array256.t;
    bp <- witness;
    mp <- witness;
    skpv <- witness;
    t <- witness;
    v <- witness;
    bp <@ __polyvec_decompress (ctp);
    ctp <- (ctp + (W64.of_int (3 * 320)));
    v <@ _poly_decompress (v, ctp);
    skpv <@ __polyvec_frombytes (skp);
    bp <@ __polyvec_ntt (bp);
    t <@ __polyvec_pointwise_acc (skpv, bp);
    t <@ _poly_invntt (t);
    mp <@ _poly_sub (mp, v, t);
    mp <@ __poly_reduce (mp);
    (msgp, mp) <@ _i_poly_tomsg (msgp, mp);
    return (msgp);
  }
  
  proc __verify (ctp:W64.t, ctpc:W8.t Array1088.t) : W64.t = {
    var aux: int;
    
    var cnd:W64.t;
    var i:int;
    var t1:W8.t;
    var t2:W8.t;
    var t64:W64.t;
    
    cnd <- (W64.of_int 0);
    aux <- ((3 * 320) + 128);
    i <- 0;
    while (i < aux) {
      t1 <- (get8_direct (WArray1088.init8 (fun i_0 => ctpc.[i_0])) i);
      t2 <- (loadW8 Glob.mem (W64.to_uint (ctp + (W64.of_int i))));
      t1 <- (t1 `^` t2);
      t64 <- (zeroextu64 t1);
      cnd <- (cnd `|` t64);
      i <- i + 1;
    }
    cnd <- (- cnd);
    cnd <- (cnd `>>` (W8.of_int 63));
    return (cnd);
  }
  
  proc __cmov (dst:W64.t, src:W8.t Array32.t, cnd:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    var t2:W8.t;
    var t1:W8.t;
    
    cnd <- (- cnd);
    i <- 0;
    while (i < 32) {
      t2 <- (loadW8 Glob.mem (W64.to_uint (dst + (W64.of_int i))));
      t1 <- (get8_direct (WArray32.init8 (fun i_0 => src.[i_0])) i);
      t2 <- (t2 `^` t1);
      t2 <- (t2 `&` (truncateu8 cnd));
      t1 <- (t1 `^` t2);
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (dst + (W64.of_int i))) (t1);
      i <- i + 1;
    }
    return ();
  }
  
  proc __crypto_kem_keypair_jazz (pkp:W64.t, skp:W64.t,
                                  randomnessp:W8.t Array64.t) : unit = {
    var aux: int;
    
    var s_randomnessp:W8.t Array64.t;
    var s_pkp:W64.t;
    var s_skp:W64.t;
    var randomnessp1:W8.t Array32.t;
    var i:int;
    var t64:W64.t;
    var h_pk:W8.t Array32.t;
    var randomnessp2:W8.t Array32.t;
    h_pk <- witness;
    randomnessp1 <- witness;
    randomnessp2 <- witness;
    s_randomnessp <- witness;
    s_randomnessp <- randomnessp;
    s_pkp <- pkp;
    s_skp <- skp;
    randomnessp1 <- (Array32.init (fun i_0 => randomnessp.[0 + i_0]));
    __indcpa_keypair (pkp, skp, randomnessp1);
    skp <- s_skp;
    skp <- (skp + (W64.of_int (3 * 384)));
    pkp <- s_pkp;
    aux <- (((3 * 384) + 32) %/ 8);
    i <- 0;
    while (i < aux) {
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int (8 * i)))) ((loadW64 Glob.mem (W64.to_uint (pkp + (W64.of_int (8 * i))))));
      i <- i + 1;
    }
    s_skp <- (s_skp + (W64.of_int ((3 * 384) + ((3 * 384) + 32))));
    pkp <- s_pkp;
    t64 <- (W64.of_int ((3 * 384) + 32));
    h_pk <@ _isha3_256 (h_pk, pkp, t64);
    skp <- s_skp;
    i <- 0;
    while (i < 4) {
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int (8 * i)))) ((get64
                                                                    (WArray32.init8 (fun i_0 => h_pk.[i_0]))
                                                                    i));
      i <- i + 1;
    }
    randomnessp <- s_randomnessp;
    randomnessp2 <- (Array32.init (fun i_0 => randomnessp.[32 + i_0]));
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int ((8 * i) + 32)))) (
      (get64 (WArray32.init8 (fun i_0 => randomnessp2.[i_0])) i));
      i <- i + 1;
    }
    return ();
  }
  
  proc __crypto_kem_enc_jazz (ctp:W64.t, shkp:W64.t, pkp:W64.t,
                              randomnessp:W8.t Array32.t) : unit = {
    var aux: int;
    var aux_0: W8.t Array32.t;
    
    var s_pkp:W64.t;
    var s_ctp:W64.t;
    var s_shkp:W64.t;
    var i:int;
    var t64:W64.t;
    var buf:W8.t Array64.t;
    var kr:W8.t Array64.t;
    buf <- witness;
    kr <- witness;
    s_pkp <- pkp;
    s_ctp <- ctp;
    s_shkp <- shkp;
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => randomnessp.[i_0])) i);
      buf <-
      Array64.init
      (WArray64.get8 (WArray64.set64 (WArray64.init8 (fun i_0 => buf.[i_0])) i (t64)));
      i <- i + 1;
    }
    pkp <- s_pkp;
    t64 <- (W64.of_int ((3 * 384) + 32));
    aux_0 <@ _isha3_256 ((Array32.init (fun i_0 => buf.[32 + i_0])), pkp,
    t64);
    buf <- Array64.init
           (fun i_0 => if 32 <= i_0 < 32 + 32 then aux_0.[i_0-32]
           else buf.[i_0]);
    kr <@ _sha3_512_64 (kr, buf);
    pkp <- s_pkp;
    __indcpa_enc (s_ctp, (Array32.init (fun i_0 => buf.[0 + i_0])), pkp,
    (Array32.init (fun i_0 => kr.[32 + i_0])));
    shkp <- s_shkp;
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray64.init8 (fun i_0 => kr.[i_0])) i);
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (shkp + (W64.of_int (8 * i)))) (t64);
      i <- i + 1;
    }
    return ();
  }
  
  proc __crypto_kem_dec_jazz (shkp:W64.t, ctp:W64.t, skp:W64.t) : unit = {
    var aux_0: int;
    var aux: W8.t Array32.t;
    
    var s_shkp:W64.t;
    var s_ctp:W64.t;
    var buf:W8.t Array64.t;
    var hp:W64.t;
    var i:int;
    var t64:W64.t;
    var s_skp:W64.t;
    var kr:W8.t Array64.t;
    var pkp:W64.t;
    var ctpc:W8.t Array1088.t;
    var cnd:W64.t;
    var s_cnd:W64.t;
    var zp:W64.t;
    buf <- witness;
    ctpc <- witness;
    kr <- witness;
    s_shkp <- shkp;
    s_ctp <- ctp;
    aux <@ __indcpa_dec ((Array32.init (fun i_0 => buf.[0 + i_0])), ctp,
    skp);
    buf <- Array64.init
           (fun i_0 => if 0 <= i_0 < 0 + 32 then aux.[i_0-0] else buf.[i_0]);
    hp <- skp;
    hp <- (hp + (W64.of_int (32 + (((24 * 3) * 256) `|>>` 3))));
    aux_0 <- (32 %/ 8);
    i <- 0;
    while (i < aux_0) {
      t64 <- (loadW64 Glob.mem (W64.to_uint (hp + (W64.of_int (8 * i)))));
      buf <-
      Array64.init
      (WArray64.get8 (WArray64.set64_direct (WArray64.init8 (fun i_0 => buf.[i_0])) (32 + (8 * i)) (t64)));
      i <- i + 1;
    }
    s_skp <- skp;
    kr <@ _sha3_512_64 (kr, buf);
    pkp <- s_skp;
    pkp <- (pkp + (W64.of_int (((12 * 3) * 256) `|>>` 3)));
    ctpc <@ __iindcpa_enc (ctpc, (Array32.init (fun i_0 => buf.[0 + i_0])),
    pkp, (Array32.init (fun i_0 => kr.[32 + i_0])));
    ctp <- s_ctp;
    cnd <@ __verify (ctp, ctpc);
    s_cnd <- cnd;
    zp <- s_skp;
    zp <- (zp + (W64.of_int 64));
    zp <- (zp + (W64.of_int (((24 * 3) * 256) `|>>` 3)));
    shkp <- s_shkp;
    _shake256_1120_32 (shkp, zp, ctp);
    shkp <- s_shkp;
    cnd <- s_cnd;
    __cmov (shkp, (Array32.init (fun i_0 => kr.[0 + i_0])), cnd);
    return ();
  }
  
  proc jade_kem_mlkem_mlkem768_amd64_ref_keypair (public_key:W64.t,
                                                  secret_key:W64.t) : 
  W64.t = {
    
    var r:W64.t;
    var randomness:W8.t Array64.t;
    var randomnessp:W8.t Array64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    randomness <- witness;
    randomnessp <- witness;
    public_key <- public_key;
    secret_key <- secret_key;
    randomnessp <- randomness;
    randomnessp <@ SC.randombytes_64 (randomnessp);
    __crypto_kem_keypair_jazz (public_key, secret_key, randomnessp);
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_64 ;
    return (r);
  }
  
  proc jade_kem_mlkem_mlkem768_amd64_ref_enc (ciphertext:W64.t,
                                              shared_secret:W64.t,
                                              public_key:W64.t) : W64.t = {
    
    var r:W64.t;
    var randomness:W8.t Array32.t;
    var randomnessp:W8.t Array32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    randomness <- witness;
    randomnessp <- witness;
    ciphertext <- ciphertext;
    shared_secret <- shared_secret;
    public_key <- public_key;
    randomnessp <- randomness;
    randomnessp <@ SC.randombytes_32 (randomnessp);
    __crypto_kem_enc_jazz (ciphertext, shared_secret, public_key,
    randomnessp);
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_64 ;
    return (r);
  }
  
  proc jade_kem_mlkem_mlkem768_amd64_ref_dec (shared_secret:W64.t,
                                              ciphertext:W64.t,
                                              secret_key:W64.t) : W64.t = {
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    __crypto_kem_dec_jazz (shared_secret, ciphertext, secret_key);
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_64 ;
    return (r);
  }
}.

