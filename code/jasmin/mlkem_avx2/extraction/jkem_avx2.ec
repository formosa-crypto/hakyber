require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array4 Array5 Array6 Array7 Array8 Array9 Array16
               Array24 Array25 Array32 Array33 Array64 Array68 Array128
               Array136 Array256 Array272 Array400 Array768 Array960
               Array1024 Array1088 Array2048 Array2304.
require import WArray8 WArray16 WArray32 WArray33 WArray40 WArray64 WArray128
               WArray136 WArray160 WArray192 WArray200 WArray224 WArray256
               WArray288 WArray512 WArray544 WArray768 WArray800 WArray960
               WArray1088 WArray1536 WArray2048 WArray2176 WArray4608.

abbrev gen_matrix_indexes = Array16.of_list witness [W16.of_int 0;
W16.of_int 1; W16.of_int 2; W16.of_int 256; W16.of_int 257; W16.of_int 258;
W16.of_int 512; W16.of_int 513; W16.of_int 0; W16.of_int 256; W16.of_int 512;
W16.of_int 1; W16.of_int 257; W16.of_int 513; W16.of_int 2; W16.of_int 258].


abbrev RATE_BIT_x4 = Array1.of_list witness [W256.of_int (-57896044618658097708646941636650613544546956437755979579936703605971808681984)].


abbrev sample_shuffle_table = Array2048.of_list witness [W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 4;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 6;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 4;
W8.of_int 6; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 6;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 8; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 8; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 8; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 8;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 4; W8.of_int 8; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 4; W8.of_int 8; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 8;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 8;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 6;
W8.of_int 8; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 8;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 8; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 8; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 10;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 4;
W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 10;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 10; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 6; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 6; W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6;
W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 6; W8.of_int 10; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 6; W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 10;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 8; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 8; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 8; W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 8;
W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 8; W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 10;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6;
W8.of_int 8; W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int 10; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int (-1); W8.of_int (-1); W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 4; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 4; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 6;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 6; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 8;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 8; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 8; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 8; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 6; W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6;
W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 8; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 8; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 6;
W8.of_int 8; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int 10;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 10; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 10; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 10; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 10; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 6; W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6;
W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 10; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 10; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 10;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 10; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 6;
W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 2; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2;
W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int 6; W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6;
W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 12;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int (-1); W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 4; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 4; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 6;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 6; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 8;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 8; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 8; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 8; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 6; W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6;
W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 8; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 8; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 6;
W8.of_int 8; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 10;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 10; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 10; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 10; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 10; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 6; W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6;
W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 10; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 10; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 10;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 10; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 6;
W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 8;
W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 8; W8.of_int 10;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 2; W8.of_int 8; W8.of_int 10; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2;
W8.of_int 8; W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 8;
W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 10;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 6; W8.of_int 8;
W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6;
W8.of_int 8; W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int 10; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int 14; W8.of_int (-1); W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 6; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 6; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 6; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 6; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int 8; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 8; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 8; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 8;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 4; W8.of_int 8; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 8; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int 6; W8.of_int 8; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 6; W8.of_int 8; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 6;
W8.of_int 8; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6; W8.of_int 8;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 6;
W8.of_int 8; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2;
W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 10; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 2; W8.of_int 10; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 10;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 4; W8.of_int 10; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 4; W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int 6; W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 6;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 2; W8.of_int 6; W8.of_int 10; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 6; W8.of_int 10; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int 4; W8.of_int 6; W8.of_int 10;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 4; W8.of_int 6; W8.of_int 10; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4;
W8.of_int 6; W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 6;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1);
W8.of_int 2; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2;
W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int (-1); W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 4; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int 0; W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int 6; W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int 0; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 2;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 2; W8.of_int 6;
W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1);
W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 12;
W8.of_int 14; W8.of_int (-1); W8.of_int (-1); W8.of_int 0; W8.of_int 4;
W8.of_int 6; W8.of_int 8; W8.of_int 10; W8.of_int 12; W8.of_int 14;
W8.of_int (-1); W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8;
W8.of_int 10; W8.of_int 12; W8.of_int 14; W8.of_int (-1); W8.of_int 0;
W8.of_int 2; W8.of_int 4; W8.of_int 6; W8.of_int 8; W8.of_int 10;
W8.of_int 12; W8.of_int 14].


abbrev sample_q = W256.of_int 5881923629679188442283784376194736327817742869488325897419002016668082834689.


abbrev sample_mask = W256.of_int 7235349132933696807194982583513801520701008426120364839270295361446620368895.


abbrev sample_ones = W256.of_int 454086624460063511464984254936031011189294057512315937409637584344757371137.


abbrev sample_load_shuffle = Array32.of_list witness [W8.of_int 0;
W8.of_int 1; W8.of_int 1; W8.of_int 2; W8.of_int 3; W8.of_int 4; W8.of_int 4;
W8.of_int 5; W8.of_int 6; W8.of_int 7; W8.of_int 7; W8.of_int 8; W8.of_int 9;
W8.of_int 10; W8.of_int 10; W8.of_int 11; W8.of_int 4; W8.of_int 5;
W8.of_int 5; W8.of_int 6; W8.of_int 7; W8.of_int 8; W8.of_int 8; W8.of_int 9;
W8.of_int 10; W8.of_int 11; W8.of_int 11; W8.of_int 12; W8.of_int 13;
W8.of_int 14; W8.of_int 14; W8.of_int 15].


abbrev KECCAK_RHOTATES_RIGHT = Array6.of_list witness [W256.of_int 144373339913893657577751063007562604548177214458152943091773;
W256.of_int 232252764209307188274174373867837442080505530800860351692863;
W256.of_int 156927543384667019098616994515559168111335794127330162507795;
W256.of_int 351517697181654122777866749001917765472957616589092975280182;
W256.of_int 276192476357013953622045746931053922384479139705868246843454;
W256.of_int 313855086769334038206421612937983674734430261968315659321364].


abbrev KECCAK_RHOTATES_LEFT = Array6.of_list witness [W256.of_int 257361171150853911329517531560668107745210100483895842570243;
W256.of_int 169481746855440380633094220700393270212881784141188433969153;
W256.of_int 244806967680080549808651600052671544182051520814718623154221;
W256.of_int 50216813883093446129401845566312946820429698352955810381834;
W256.of_int 125542034707733615285222847637176789908908175236180538818562;
W256.of_int 87879424295413530700846981630247037558957052973733126340652].


abbrev KECCAK_IOTAS = Array24.of_list witness [W256.of_int 6277101735386680764176071790128604879584176795969512275969;
W256.of_int 206504092890751023779864409751650843328560248233805014854828162;
W256.of_int (-57896044618657891154337237002533387566728630465883811983015055433200855646070);
W256.of_int (-57896044605177918687001956587831074660851270707671256656745893357814858874880);
W256.of_int 206560586806369503906741994397762000772476505824968740465311883;
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891964083360867415206145441891392473841449373862113267939246071);
W256.of_int 866240039483361945456297907037747473382616397843792694083722;
W256.of_int 853685836012588583927945763457490263623448044251853669531784;
W256.of_int 13480179078138900667299665761280331841242166839448401411882560290825;
W256.of_int 13479973396346337251931066003935984697246077504727327878873813614602;
W256.of_int 13480179894162126267568165104169664557960801185391384887919156166795;
W256.of_int (-57896044618658096836129800417901987324072977609879901317736128966209602322293);
W256.of_int (-57896044618657891160614338737920068330904702256012416862599232229170367922039);
W256.of_int (-57896044618657892001745971279735290730498322133245470726878922889085012901885);
W256.of_int (-57896044618657892008023073015121971494674393923374075606463099685054525177854);
W256.of_int (-57896044618658096905177919507155475730009767301294554993162073721874237357952);
W256.of_int 205750840682504622088163281136835410743010147018288673381711882;
W256.of_int (-57896044605178124312300604384719547540610971740509902075209375727097995067382);
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891217108254356400195208489348367169860778856823392895978405760);
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177918636785142704737628547442696386642417620072478990058760667128)].


abbrev ROL8 = W256.of_int 13620818001941277694121380808605999856886653716761013959207994299728839901191.


abbrev ROL56 = W256.of_int 10910488462195273559651782724632284871561478246514020268633800075540923875841.


abbrev KECCAK1600_RC_AVX2 = Array24.of_list witness [W256.of_int 6277101735386680764176071790128604879584176795969512275969;
W256.of_int 206504092890751023779864409751650843328560248233805014854828162;
W256.of_int (-57896044618657891154337237002533387566728630465883811983015055433200855646070);
W256.of_int (-57896044605177918687001956587831074660851270707671256656745893357814858874880);
W256.of_int 206560586806369503906741994397762000772476505824968740465311883;
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891964083360867415206145441891392473841449373862113267939246071);
W256.of_int 866240039483361945456297907037747473382616397843792694083722;
W256.of_int 853685836012588583927945763457490263623448044251853669531784;
W256.of_int 13480179078138900667299665761280331841242166839448401411882560290825;
W256.of_int 13479973396346337251931066003935984697246077504727327878873813614602;
W256.of_int 13480179894162126267568165104169664557960801185391384887919156166795;
W256.of_int (-57896044618658096836129800417901987324072977609879901317736128966209602322293);
W256.of_int (-57896044618657891160614338737920068330904702256012416862599232229170367922039);
W256.of_int (-57896044618657892001745971279735290730498322133245470726878922889085012901885);
W256.of_int (-57896044618657892008023073015121971494674393923374075606463099685054525177854);
W256.of_int (-57896044618658096905177919507155475730009767301294554993162073721874237357952);
W256.of_int 205750840682504622088163281136835410743010147018288673381711882;
W256.of_int (-57896044605178124312300604384719547540610971740509902075209375727097995067382);
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891217108254356400195208489348367169860778856823392895978405760);
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177918636785142704737628547442696386642417620072478990058760667128)].


abbrev pvc_shufbidx_s = Array32.of_list witness [W8.of_int 0; W8.of_int 1;
W8.of_int 2; W8.of_int 3; W8.of_int 4; W8.of_int 8; W8.of_int 9;
W8.of_int 10; W8.of_int 11; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 9;
W8.of_int 10; W8.of_int 11; W8.of_int 12; W8.of_int (-1); W8.of_int (-1);
W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int (-1); W8.of_int 0;
W8.of_int 1; W8.of_int 2; W8.of_int 3; W8.of_int 4; W8.of_int 8].


abbrev pvc_sllvdidx_s = W64.of_int 12.


abbrev pvc_shift2_s = W64.of_int 288230380513787905.


abbrev pvc_mask_s = W16.of_int 1023.


abbrev pvc_shift1_s = W16.of_int 4096.


abbrev pvc_off_s = W16.of_int 15.


abbrev pvd_mask_s = W32.of_int 2145394680.


abbrev pvd_sllvdidx_s = W64.of_int 4.


abbrev pvd_shufbdidx_s = Array32.of_list witness [W8.of_int 0; W8.of_int 1;
W8.of_int 1; W8.of_int 2; W8.of_int 2; W8.of_int 3; W8.of_int 3; W8.of_int 4;
W8.of_int 5; W8.of_int 6; W8.of_int 6; W8.of_int 7; W8.of_int 7; W8.of_int 8;
W8.of_int 8; W8.of_int 9; W8.of_int 2; W8.of_int 3; W8.of_int 3; W8.of_int 4;
W8.of_int 4; W8.of_int 5; W8.of_int 5; W8.of_int 6; W8.of_int 7; W8.of_int 8;
W8.of_int 8; W8.of_int 9; W8.of_int 9; W8.of_int 10; W8.of_int 10;
W8.of_int 11].


abbrev pvd_q_s = W32.of_int 218182660.


abbrev cbd_jshufbidx = Array32.of_list witness [W8.of_int 0; W8.of_int 1;
W8.of_int 2; W8.of_int (-1); W8.of_int 3; W8.of_int 4; W8.of_int 5;
W8.of_int (-1); W8.of_int 6; W8.of_int 7; W8.of_int 8; W8.of_int (-1);
W8.of_int 9; W8.of_int 10; W8.of_int 11; W8.of_int (-1); W8.of_int 4;
W8.of_int 5; W8.of_int 6; W8.of_int (-1); W8.of_int 7; W8.of_int 8;
W8.of_int 9; W8.of_int (-1); W8.of_int 10; W8.of_int 11; W8.of_int 12;
W8.of_int (-1); W8.of_int 13; W8.of_int 14; W8.of_int 15; W8.of_int (-1)].


abbrev pfm_idx_s = Array16.of_list witness [W8.of_int 0; W8.of_int 1;
W8.of_int 4; W8.of_int 5; W8.of_int 8; W8.of_int 9; W8.of_int 12;
W8.of_int 13; W8.of_int 2; W8.of_int 3; W8.of_int 6; W8.of_int 7;
W8.of_int 10; W8.of_int 11; W8.of_int 14; W8.of_int 15].


abbrev pfm_shift_s = Array4.of_list witness [W32.of_int 3; W32.of_int 2;
W32.of_int 1; W32.of_int 0].


abbrev pd_shift_s = W32.of_int 8390656.


abbrev pd_mask_s = W32.of_int 15728655.


abbrev pd_jshufbidx = Array32.of_list witness [W8.of_int 0; W8.of_int 0;
W8.of_int 0; W8.of_int 0; W8.of_int 1; W8.of_int 1; W8.of_int 1; W8.of_int 1;
W8.of_int 2; W8.of_int 2; W8.of_int 2; W8.of_int 2; W8.of_int 3; W8.of_int 3;
W8.of_int 3; W8.of_int 3; W8.of_int 4; W8.of_int 4; W8.of_int 4; W8.of_int 4;
W8.of_int 5; W8.of_int 5; W8.of_int 5; W8.of_int 5; W8.of_int 6; W8.of_int 6;
W8.of_int 6; W8.of_int 6; W8.of_int 7; W8.of_int 7; W8.of_int 7;
W8.of_int 7].


abbrev pc_permidx_s = Array8.of_list witness [W32.of_int 0; W32.of_int 4;
W32.of_int 1; W32.of_int 5; W32.of_int 2; W32.of_int 6; W32.of_int 3;
W32.of_int 7].


abbrev pc_shift2_s = W16.of_int 4097.


abbrev pc_mask_s = W16.of_int 15.


abbrev pc_shift1_s = W16.of_int 512.


abbrev KeccakF1600RoundConstants = Array24.of_list witness [W256.of_int 6277101735386680764176071790128604879584176795969512275969;
W256.of_int 206504092890751023779864409751650843328560248233805014854828162;
W256.of_int (-57896044618657891154337237002533387566728630465883811983015055433200855646070);
W256.of_int (-57896044605177918687001956587831074660851270707671256656745893357814858874880);
W256.of_int 206560586806369503906741994397762000772476505824968740465311883;
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891964083360867415206145441891392473841449373862113267939246071);
W256.of_int 866240039483361945456297907037747473382616397843792694083722;
W256.of_int 853685836012588583927945763457490263623448044251853669531784;
W256.of_int 13480179078138900667299665761280331841242166839448401411882560290825;
W256.of_int 13479973396346337251931066003935984697246077504727327878873813614602;
W256.of_int 13480179894162126267568165104169664557960801185391384887919156166795;
W256.of_int (-57896044618658096836129800417901987324072977609879901317736128966209602322293);
W256.of_int (-57896044618657891160614338737920068330904702256012416862599232229170367922039);
W256.of_int (-57896044618657892001745971279735290730498322133245470726878922889085012901885);
W256.of_int (-57896044618657892008023073015121971494674393923374075606463099685054525177854);
W256.of_int (-57896044618658096905177919507155475730009767301294554993162073721874237357952);
W256.of_int 205750840682504622088163281136835410743010147018288673381711882;
W256.of_int (-57896044605178124312300604384719547540610971740509902075209375727097995067382);
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891217108254356400195208489348367169860778856823392895978405760);
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177918636785142704737628547442696386642417620072478990058760667128)].


abbrev rho8 = W256.of_int 13620818001941277694121380808605999856886653716761013959207994299728839901191.


abbrev rho56 = W256.of_int 10910488462195273559651782724632284871561478246514020268633800075540923875841.


abbrev shake_sep = Array4.of_list witness [W64.of_int (-9223372036854775808);
W64.of_int (-9223372036854775808); W64.of_int (-9223372036854775808);
W64.of_int (-9223372036854775808)].


abbrev KECCAK1600_RC = Array24.of_list witness [W64.of_int 1;
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


abbrev jdmontx16 = Array16.of_list witness [W16.of_int 1353; W16.of_int 1353;
W16.of_int 1353; W16.of_int 1353; W16.of_int 1353; W16.of_int 1353;
W16.of_int 1353; W16.of_int 1353; W16.of_int 1353; W16.of_int 1353;
W16.of_int 1353; W16.of_int 1353; W16.of_int 1353; W16.of_int 1353;
W16.of_int 1353; W16.of_int 1353].


abbrev mqinvx16 = Array16.of_list witness [W16.of_int 15099;
W16.of_int 15099; W16.of_int 15099; W16.of_int 15099; W16.of_int 15099;
W16.of_int 15099; W16.of_int 15099; W16.of_int 15099; W16.of_int 15099;
W16.of_int 15099; W16.of_int 15099; W16.of_int 15099; W16.of_int 15099;
W16.of_int 15099; W16.of_int 15099; W16.of_int 15099].


abbrev hhqx16 = Array16.of_list witness [W16.of_int 832; W16.of_int 832;
W16.of_int 832; W16.of_int 832; W16.of_int 832; W16.of_int 832;
W16.of_int 832; W16.of_int 832; W16.of_int 832; W16.of_int 832;
W16.of_int 832; W16.of_int 832; W16.of_int 832; W16.of_int 832;
W16.of_int 832; W16.of_int 832].


abbrev hqx16_m1 = Array16.of_list witness [W16.of_int 1664; W16.of_int 1664;
W16.of_int 1664; W16.of_int 1664; W16.of_int 1664; W16.of_int 1664;
W16.of_int 1664; W16.of_int 1664; W16.of_int 1664; W16.of_int 1664;
W16.of_int 1664; W16.of_int 1664; W16.of_int 1664; W16.of_int 1664;
W16.of_int 1664; W16.of_int 1664].


abbrev hqx16_p1 = Array16.of_list witness [W16.of_int 1665; W16.of_int 1665;
W16.of_int 1665; W16.of_int 1665; W16.of_int 1665; W16.of_int 1665;
W16.of_int 1665; W16.of_int 1665; W16.of_int 1665; W16.of_int 1665;
W16.of_int 1665; W16.of_int 1665; W16.of_int 1665; W16.of_int 1665;
W16.of_int 1665; W16.of_int 1665].


abbrev maskx16 = Array16.of_list witness [W16.of_int 4095; W16.of_int 4095;
W16.of_int 4095; W16.of_int 4095; W16.of_int 4095; W16.of_int 4095;
W16.of_int 4095; W16.of_int 4095; W16.of_int 4095; W16.of_int 4095;
W16.of_int 4095; W16.of_int 4095; W16.of_int 4095; W16.of_int 4095;
W16.of_int 4095; W16.of_int 4095].


abbrev jflox16 = Array16.of_list witness [W16.of_int (-10079);
W16.of_int (-10079); W16.of_int (-10079); W16.of_int (-10079);
W16.of_int (-10079); W16.of_int (-10079); W16.of_int (-10079);
W16.of_int (-10079); W16.of_int (-10079); W16.of_int (-10079);
W16.of_int (-10079); W16.of_int (-10079); W16.of_int (-10079);
W16.of_int (-10079); W16.of_int (-10079); W16.of_int (-10079)].


abbrev jfhix16 = Array16.of_list witness [W16.of_int 1441; W16.of_int 1441;
W16.of_int 1441; W16.of_int 1441; W16.of_int 1441; W16.of_int 1441;
W16.of_int 1441; W16.of_int 1441; W16.of_int 1441; W16.of_int 1441;
W16.of_int 1441; W16.of_int 1441; W16.of_int 1441; W16.of_int 1441;
W16.of_int 1441; W16.of_int 1441].


abbrev jvx16 = Array16.of_list witness [W16.of_int 20159; W16.of_int 20159;
W16.of_int 20159; W16.of_int 20159; W16.of_int 20159; W16.of_int 20159;
W16.of_int 20159; W16.of_int 20159; W16.of_int 20159; W16.of_int 20159;
W16.of_int 20159; W16.of_int 20159; W16.of_int 20159; W16.of_int 20159;
W16.of_int 20159; W16.of_int 20159].


abbrev jqinvx16 = Array16.of_list witness [W16.of_int (-3327);
W16.of_int (-3327); W16.of_int (-3327); W16.of_int (-3327);
W16.of_int (-3327); W16.of_int (-3327); W16.of_int (-3327);
W16.of_int (-3327); W16.of_int (-3327); W16.of_int (-3327);
W16.of_int (-3327); W16.of_int (-3327); W16.of_int (-3327);
W16.of_int (-3327); W16.of_int (-3327); W16.of_int (-3327)].


abbrev jqx16 = Array16.of_list witness [W16.of_int 3329; W16.of_int 3329;
W16.of_int 3329; W16.of_int 3329; W16.of_int 3329; W16.of_int 3329;
W16.of_int 3329; W16.of_int 3329; W16.of_int 3329; W16.of_int 3329;
W16.of_int 3329; W16.of_int 3329; W16.of_int 3329; W16.of_int 3329;
W16.of_int 3329; W16.of_int 3329].


abbrev jzetas_inv_exp = Array400.of_list witness [W16.of_int (-23131);
W16.of_int (-7756); W16.of_int 20258; W16.of_int 23860; W16.of_int 17443;
W16.of_int (-23210); W16.of_int 20199; W16.of_int 21498; W16.of_int (-14469);
W16.of_int 11045; W16.of_int 14903; W16.of_int 6280; W16.of_int 32385;
W16.of_int (-15355); W16.of_int (-2145); W16.of_int (-20296);
W16.of_int 1701; W16.of_int 1460; W16.of_int 2338; W16.of_int 308;
W16.of_int 2851; W16.of_int 854; W16.of_int 2535; W16.of_int 1530;
W16.of_int 1659; W16.of_int 3109; W16.of_int 1335; W16.of_int 136;
W16.of_int 2945; W16.of_int 1285; W16.of_int 2719; W16.of_int 2232;
W16.of_int 17423; W16.of_int (-23997); W16.of_int (-28643);
W16.of_int (-31636); W16.of_int (-10906); W16.of_int 22502; W16.of_int 7934;
W16.of_int (-10335); W16.of_int (-16989); W16.of_int (-24214);
W16.of_int (-10945); W16.of_int 20927; W16.of_int (-24391); W16.of_int 7383;
W16.of_int (-25434); W16.of_int 31184; W16.of_int 1807; W16.of_int 2371;
W16.of_int 2333; W16.of_int 108; W16.of_int 870; W16.of_int 1510;
W16.of_int 1278; W16.of_int 1185; W16.of_int 1187; W16.of_int 874;
W16.of_int 2111; W16.of_int 1215; W16.of_int 1465; W16.of_int 2007;
W16.of_int 2726; W16.of_int 2512; W16.of_int 17915; W16.of_int 24156;
W16.of_int (-4311); W16.of_int (-16831); W16.of_int 12757; W16.of_int 29156;
W16.of_int (-14016); W16.of_int (-13426); W16.of_int (-18249);
W16.of_int 30199; W16.of_int (-9075); W16.of_int 28310; W16.of_int 8899;
W16.of_int 15887; W16.of_int 28250; W16.of_int (-19883); W16.of_int 1275;
W16.of_int 2652; W16.of_int 1065; W16.of_int 2881; W16.of_int 725;
W16.of_int 1508; W16.of_int 2368; W16.of_int 398; W16.of_int 951;
W16.of_int 247; W16.of_int 1421; W16.of_int 3222; W16.of_int 2499;
W16.of_int 271; W16.of_int 90; W16.of_int 853; W16.of_int 16163;
W16.of_int 16163; W16.of_int (-26675); W16.of_int (-26675);
W16.of_int (-8858); W16.of_int (-8858); W16.of_int (-18426);
W16.of_int (-18426); W16.of_int (-8799); W16.of_int (-8799);
W16.of_int 10533; W16.of_int 10533; W16.of_int (-24312); W16.of_int (-24312);
W16.of_int 28073; W16.of_int 28073; W16.of_int 1571; W16.of_int 1571;
W16.of_int 205; W16.of_int 205; W16.of_int 2918; W16.of_int 2918;
W16.of_int 1542; W16.of_int 1542; W16.of_int 2721; W16.of_int 2721;
W16.of_int 2597; W16.of_int 2597; W16.of_int 2312; W16.of_int 2312;
W16.of_int 681; W16.of_int 681; W16.of_int (-31163); W16.of_int (-31163);
W16.of_int (-31163); W16.of_int (-31163); W16.of_int 11202; W16.of_int 11202;
W16.of_int 11202; W16.of_int 11202; W16.of_int (-1358); W16.of_int (-1358);
W16.of_int (-1358); W16.of_int (-1358); W16.of_int (-10689);
W16.of_int (-10689); W16.of_int (-10689); W16.of_int (-10689);
W16.of_int 1861; W16.of_int 1861; W16.of_int 1861; W16.of_int 1861;
W16.of_int 1474; W16.of_int 1474; W16.of_int 1474; W16.of_int 1474;
W16.of_int 1202; W16.of_int 1202; W16.of_int 1202; W16.of_int 1202;
W16.of_int 2367; W16.of_int 2367; W16.of_int 2367; W16.of_int 2367;
W16.of_int 16695; W16.of_int 16695; W16.of_int 16695; W16.of_int 16695;
W16.of_int 16695; W16.of_int 16695; W16.of_int 16695; W16.of_int 16695;
W16.of_int (-28190); W16.of_int (-28190); W16.of_int (-28190);
W16.of_int (-28190); W16.of_int (-28190); W16.of_int (-28190);
W16.of_int (-28190); W16.of_int (-28190); W16.of_int 3127; W16.of_int 3127;
W16.of_int 3127; W16.of_int 3127; W16.of_int 3127; W16.of_int 3127;
W16.of_int 3127; W16.of_int 3127; W16.of_int 3042; W16.of_int 3042;
W16.of_int 3042; W16.of_int 3042; W16.of_int 3042; W16.of_int 3042;
W16.of_int 3042; W16.of_int 3042; W16.of_int (-787); W16.of_int (-787);
W16.of_int 1517; W16.of_int 1517; W16.of_int 12619; W16.of_int (-19528);
W16.of_int (-18524); W16.of_int (-20099); W16.of_int (-12638);
W16.of_int 18742; W16.of_int (-30317); W16.of_int 32503; W16.of_int (-5492);
W16.of_int (-23092); W16.of_int 4587; W16.of_int (-13130); W16.of_int 21656;
W16.of_int 14234; W16.of_int (-13386); W16.of_int (-11181); W16.of_int 75;
W16.of_int 3000; W16.of_int 2980; W16.of_int 2685; W16.of_int 2210;
W16.of_int 1846; W16.of_int 147; W16.of_int 2551; W16.of_int 1676;
W16.of_int 460; W16.of_int 235; W16.of_int 2742; W16.of_int 3224;
W16.of_int 2458; W16.of_int 2486; W16.of_int 2899; W16.of_int 5276;
W16.of_int 14431; W16.of_int (-17560); W16.of_int 18486; W16.of_int 28762;
W16.of_int (-29175); W16.of_int (-10630); W16.of_int (-32010);
W16.of_int (-6181); W16.of_int 14883; W16.of_int (-944); W16.of_int 27739;
W16.of_int (-20493); W16.of_int 32227; W16.of_int 11478; W16.of_int 335;
W16.of_int 156; W16.of_int 2911; W16.of_int 872; W16.of_int 1590;
W16.of_int 602; W16.of_int 777; W16.of_int 2170; W16.of_int 246;
W16.of_int 1755; W16.of_int 291; W16.of_int 3152; W16.of_int 2907;
W16.of_int 1779; W16.of_int 1251; W16.of_int 2774; W16.of_int 1103;
W16.of_int (-27836); W16.of_int 25987; W16.of_int 650; W16.of_int (-9134);
W16.of_int 12442; W16.of_int (-16064); W16.of_int (-26616); W16.of_int 12797;
W16.of_int (-25080); W16.of_int (-20710); W16.of_int (-20178);
W16.of_int 23565; W16.of_int (-30966); W16.of_int (-1496); W16.of_int 6517;
W16.of_int 5690; W16.of_int 1860; W16.of_int 3203; W16.of_int 1162;
W16.of_int 1618; W16.of_int 666; W16.of_int 320; W16.of_int 8;
W16.of_int 2813; W16.of_int 1544; W16.of_int 282; W16.of_int 1838;
W16.of_int 1293; W16.of_int 2314; W16.of_int 552; W16.of_int 2677;
W16.of_int 2106; W16.of_int 26242; W16.of_int 26242; W16.of_int (-21438);
W16.of_int (-21438); W16.of_int 1103; W16.of_int 1103; W16.of_int (-5571);
W16.of_int (-5571); W16.of_int 29058; W16.of_int 29058; W16.of_int 26361;
W16.of_int 26361; W16.of_int (-17363); W16.of_int (-17363); W16.of_int 5828;
W16.of_int 5828; W16.of_int 130; W16.of_int 130; W16.of_int 1602;
W16.of_int 1602; W16.of_int 1871; W16.of_int 1871; W16.of_int 829;
W16.of_int 829; W16.of_int 2946; W16.of_int 2946; W16.of_int 3065;
W16.of_int 3065; W16.of_int 1325; W16.of_int 1325; W16.of_int 2756;
W16.of_int 2756; W16.of_int 15691; W16.of_int 15691; W16.of_int 15691;
W16.of_int 15691; W16.of_int 3800; W16.of_int 3800; W16.of_int 3800;
W16.of_int 3800; W16.of_int (-27757); W16.of_int (-27757);
W16.of_int (-27757); W16.of_int (-27757); W16.of_int 20907; W16.of_int 20907;
W16.of_int 20907; W16.of_int 20907; W16.of_int 3147; W16.of_int 3147;
W16.of_int 3147; W16.of_int 3147; W16.of_int 1752; W16.of_int 1752;
W16.of_int 1752; W16.of_int 1752; W16.of_int 2707; W16.of_int 2707;
W16.of_int 2707; W16.of_int 2707; W16.of_int 171; W16.of_int 171;
W16.of_int 171; W16.of_int 171; W16.of_int 12403; W16.of_int 12403;
W16.of_int 12403; W16.of_int 12403; W16.of_int 12403; W16.of_int 12403;
W16.of_int 12403; W16.of_int 12403; W16.of_int (-13524); W16.of_int (-13524);
W16.of_int (-13524); W16.of_int (-13524); W16.of_int (-13524);
W16.of_int (-13524); W16.of_int (-13524); W16.of_int (-13524);
W16.of_int 1907; W16.of_int 1907; W16.of_int 1907; W16.of_int 1907;
W16.of_int 1907; W16.of_int 1907; W16.of_int 1907; W16.of_int 1907;
W16.of_int 1836; W16.of_int 1836; W16.of_int 1836; W16.of_int 1836;
W16.of_int 1836; W16.of_int 1836; W16.of_int 1836; W16.of_int 1836;
W16.of_int (-14745); W16.of_int (-14745); W16.of_int 359; W16.of_int 359;
W16.of_int (-5236); W16.of_int (-5236); W16.of_int 1932; W16.of_int 1932;
W16.of_int 0; W16.of_int 0; W16.of_int 0; W16.of_int 0].


abbrev jzetas_exp = Array400.of_list witness [W16.of_int 31499;
W16.of_int 31499; W16.of_int 2571; W16.of_int 2571; W16.of_int 14746;
W16.of_int 14746; W16.of_int 2970; W16.of_int 2970; W16.of_int 13525;
W16.of_int 13525; W16.of_int 13525; W16.of_int 13525; W16.of_int 13525;
W16.of_int 13525; W16.of_int 13525; W16.of_int 13525; W16.of_int (-12402);
W16.of_int (-12402); W16.of_int (-12402); W16.of_int (-12402);
W16.of_int (-12402); W16.of_int (-12402); W16.of_int (-12402);
W16.of_int (-12402); W16.of_int 1493; W16.of_int 1493; W16.of_int 1493;
W16.of_int 1493; W16.of_int 1493; W16.of_int 1493; W16.of_int 1493;
W16.of_int 1493; W16.of_int 1422; W16.of_int 1422; W16.of_int 1422;
W16.of_int 1422; W16.of_int 1422; W16.of_int 1422; W16.of_int 1422;
W16.of_int 1422; W16.of_int (-20906); W16.of_int (-20906);
W16.of_int (-20906); W16.of_int (-20906); W16.of_int 27758; W16.of_int 27758;
W16.of_int 27758; W16.of_int 27758; W16.of_int (-3799); W16.of_int (-3799);
W16.of_int (-3799); W16.of_int (-3799); W16.of_int (-15690);
W16.of_int (-15690); W16.of_int (-15690); W16.of_int (-15690);
W16.of_int 3158; W16.of_int 3158; W16.of_int 3158; W16.of_int 3158;
W16.of_int 622; W16.of_int 622; W16.of_int 622; W16.of_int 622;
W16.of_int 1577; W16.of_int 1577; W16.of_int 1577; W16.of_int 1577;
W16.of_int 182; W16.of_int 182; W16.of_int 182; W16.of_int 182;
W16.of_int (-5827); W16.of_int (-5827); W16.of_int 17364; W16.of_int 17364;
W16.of_int (-26360); W16.of_int (-26360); W16.of_int (-29057);
W16.of_int (-29057); W16.of_int 5572; W16.of_int 5572; W16.of_int (-1102);
W16.of_int (-1102); W16.of_int 21439; W16.of_int 21439; W16.of_int (-26241);
W16.of_int (-26241); W16.of_int 573; W16.of_int 573; W16.of_int 2004;
W16.of_int 2004; W16.of_int 264; W16.of_int 264; W16.of_int 383;
W16.of_int 383; W16.of_int 2500; W16.of_int 2500; W16.of_int 1458;
W16.of_int 1458; W16.of_int 1727; W16.of_int 1727; W16.of_int 3199;
W16.of_int 3199; W16.of_int (-5689); W16.of_int (-6516); W16.of_int 1497;
W16.of_int 30967; W16.of_int (-23564); W16.of_int 20179; W16.of_int 20711;
W16.of_int 25081; W16.of_int (-12796); W16.of_int 26617; W16.of_int 16065;
W16.of_int (-12441); W16.of_int 9135; W16.of_int (-649); W16.of_int (-25986);
W16.of_int 27837; W16.of_int 1223; W16.of_int 652; W16.of_int 2777;
W16.of_int 1015; W16.of_int 2036; W16.of_int 1491; W16.of_int 3047;
W16.of_int 1785; W16.of_int 516; W16.of_int 3321; W16.of_int 3009;
W16.of_int 2663; W16.of_int 1711; W16.of_int 2167; W16.of_int 126;
W16.of_int 1469; W16.of_int (-334); W16.of_int (-11477); W16.of_int (-32226);
W16.of_int 20494; W16.of_int (-27738); W16.of_int 945; W16.of_int (-14882);
W16.of_int 6182; W16.of_int 32011; W16.of_int 10631; W16.of_int 29176;
W16.of_int (-28761); W16.of_int (-18485); W16.of_int 17561;
W16.of_int (-14430); W16.of_int (-5275); W16.of_int 2226; W16.of_int 555;
W16.of_int 2078; W16.of_int 1550; W16.of_int 422; W16.of_int 177;
W16.of_int 3038; W16.of_int 1574; W16.of_int 3083; W16.of_int 1159;
W16.of_int 2552; W16.of_int 2727; W16.of_int 1739; W16.of_int 2457;
W16.of_int 418; W16.of_int 3173; W16.of_int 11182; W16.of_int 13387;
W16.of_int (-14233); W16.of_int (-21655); W16.of_int 13131;
W16.of_int (-4586); W16.of_int 23093; W16.of_int 5493; W16.of_int (-32502);
W16.of_int 30318; W16.of_int (-18741); W16.of_int 12639; W16.of_int 20100;
W16.of_int 18525; W16.of_int 19529; W16.of_int (-12618); W16.of_int 430;
W16.of_int 843; W16.of_int 871; W16.of_int 105; W16.of_int 587;
W16.of_int 3094; W16.of_int 2869; W16.of_int 1653; W16.of_int 778;
W16.of_int 3182; W16.of_int 1483; W16.of_int 1119; W16.of_int 644;
W16.of_int 349; W16.of_int 329; W16.of_int 3254; W16.of_int 788;
W16.of_int 788; W16.of_int 1812; W16.of_int 1812; W16.of_int 28191;
W16.of_int 28191; W16.of_int 28191; W16.of_int 28191; W16.of_int 28191;
W16.of_int 28191; W16.of_int 28191; W16.of_int 28191; W16.of_int (-16694);
W16.of_int (-16694); W16.of_int (-16694); W16.of_int (-16694);
W16.of_int (-16694); W16.of_int (-16694); W16.of_int (-16694);
W16.of_int (-16694); W16.of_int 287; W16.of_int 287; W16.of_int 287;
W16.of_int 287; W16.of_int 287; W16.of_int 287; W16.of_int 287;
W16.of_int 287; W16.of_int 202; W16.of_int 202; W16.of_int 202;
W16.of_int 202; W16.of_int 202; W16.of_int 202; W16.of_int 202;
W16.of_int 202; W16.of_int 10690; W16.of_int 10690; W16.of_int 10690;
W16.of_int 10690; W16.of_int 1359; W16.of_int 1359; W16.of_int 1359;
W16.of_int 1359; W16.of_int (-11201); W16.of_int (-11201);
W16.of_int (-11201); W16.of_int (-11201); W16.of_int 31164; W16.of_int 31164;
W16.of_int 31164; W16.of_int 31164; W16.of_int 962; W16.of_int 962;
W16.of_int 962; W16.of_int 962; W16.of_int 2127; W16.of_int 2127;
W16.of_int 2127; W16.of_int 2127; W16.of_int 1855; W16.of_int 1855;
W16.of_int 1855; W16.of_int 1855; W16.of_int 1468; W16.of_int 1468;
W16.of_int 1468; W16.of_int 1468; W16.of_int (-28072); W16.of_int (-28072);
W16.of_int 24313; W16.of_int 24313; W16.of_int (-10532); W16.of_int (-10532);
W16.of_int 8800; W16.of_int 8800; W16.of_int 18427; W16.of_int 18427;
W16.of_int 8859; W16.of_int 8859; W16.of_int 26676; W16.of_int 26676;
W16.of_int (-16162); W16.of_int (-16162); W16.of_int 2648; W16.of_int 2648;
W16.of_int 1017; W16.of_int 1017; W16.of_int 732; W16.of_int 732;
W16.of_int 608; W16.of_int 608; W16.of_int 1787; W16.of_int 1787;
W16.of_int 411; W16.of_int 411; W16.of_int 3124; W16.of_int 3124;
W16.of_int 1758; W16.of_int 1758; W16.of_int 19884; W16.of_int (-28249);
W16.of_int (-15886); W16.of_int (-8898); W16.of_int (-28309);
W16.of_int 9076; W16.of_int (-30198); W16.of_int 18250; W16.of_int 13427;
W16.of_int 14017; W16.of_int (-29155); W16.of_int (-12756); W16.of_int 16832;
W16.of_int 4312; W16.of_int (-24155); W16.of_int (-17914); W16.of_int 2476;
W16.of_int 3239; W16.of_int 3058; W16.of_int 830; W16.of_int 107;
W16.of_int 1908; W16.of_int 3082; W16.of_int 2378; W16.of_int 2931;
W16.of_int 961; W16.of_int 1821; W16.of_int 2604; W16.of_int 448;
W16.of_int 2264; W16.of_int 677; W16.of_int 2054; W16.of_int (-31183);
W16.of_int 25435; W16.of_int (-7382); W16.of_int 24392; W16.of_int (-20926);
W16.of_int 10946; W16.of_int 24215; W16.of_int 16990; W16.of_int 10336;
W16.of_int (-7933); W16.of_int (-22501); W16.of_int 10907; W16.of_int 31637;
W16.of_int 28644; W16.of_int 23998; W16.of_int (-17422); W16.of_int 817;
W16.of_int 603; W16.of_int 1322; W16.of_int 1864; W16.of_int 2114;
W16.of_int 1218; W16.of_int 2455; W16.of_int 2142; W16.of_int 2144;
W16.of_int 2051; W16.of_int 1819; W16.of_int 2459; W16.of_int 3221;
W16.of_int 996; W16.of_int 958; W16.of_int 1522; W16.of_int 20297;
W16.of_int 2146; W16.of_int 15356; W16.of_int (-32384); W16.of_int (-6279);
W16.of_int (-14902); W16.of_int (-11044); W16.of_int 14470;
W16.of_int (-21497); W16.of_int (-20198); W16.of_int 23211;
W16.of_int (-17442); W16.of_int (-23859); W16.of_int (-20257);
W16.of_int 7757; W16.of_int 23132; W16.of_int 1097; W16.of_int 610;
W16.of_int 2044; W16.of_int 384; W16.of_int 3193; W16.of_int 1994;
W16.of_int 220; W16.of_int 1670; W16.of_int 1799; W16.of_int 794;
W16.of_int 2475; W16.of_int 478; W16.of_int 3021; W16.of_int 991;
W16.of_int 1869; W16.of_int 1628; W16.of_int 0; W16.of_int 0; W16.of_int 0;
W16.of_int 0].


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
  proc __shuffle8 (a:W256.t, b:W256.t) : W256.t * W256.t = {
    
    var r0:W256.t;
    var r1:W256.t;
    
    r0 <- VPERM2I128 a b (W8.of_int 32);
    r1 <- VPERM2I128 a b (W8.of_int 49);
    return (r0, r1);
  }
  
  proc __shuffle4 (a:W256.t, b:W256.t) : W256.t * W256.t = {
    
    var r0:W256.t;
    var r1:W256.t;
    
    r0 <- VPUNPCKL_4u64 a b;
    r1 <- VPUNPCKH_4u64 a b;
    return (r0, r1);
  }
  
  proc __shuffle2 (a:W256.t, b:W256.t) : W256.t * W256.t = {
    
    var t0:W256.t;
    var t1:W256.t;
    
    t0 <- VMOVSLDUP_256 b;
    t0 <- VPBLEND_8u32 a t0 (W8.of_int 170);
    a <- VPSRL_4u64 a (W8.of_int 32);
    t1 <- VPBLEND_8u32 a b (W8.of_int 170);
    return (t0, t1);
  }
  
  proc __shuffle1 (a:W256.t, b:W256.t) : W256.t * W256.t = {
    
    var r0:W256.t;
    var r1:W256.t;
    var t0:W256.t;
    var t1:W256.t;
    
    t0 <- VPSLL_8u32 b (W8.of_int 16);
    r0 <- VPBLEND_16u16 a t0 (W8.of_int 170);
    t1 <- VPSRL_8u32 a (W8.of_int 16);
    r1 <- VPBLEND_16u16 t1 b (W8.of_int 170);
    return (r0, r1);
  }
  
  proc __nttunpack128 (r0:W256.t, r1:W256.t, r2:W256.t, r3:W256.t, r4:W256.t,
                       r5:W256.t, r6:W256.t, r7:W256.t) : W256.t * W256.t *
                                                          W256.t * W256.t *
                                                          W256.t * W256.t *
                                                          W256.t * W256.t = {
    
    
    
    (r0, r4) <@ __shuffle8 (r0, r4);
    (r1, r5) <@ __shuffle8 (r1, r5);
    (r2, r6) <@ __shuffle8 (r2, r6);
    (r3, r7) <@ __shuffle8 (r3, r7);
    (r0, r2) <@ __shuffle4 (r0, r2);
    (r4, r6) <@ __shuffle4 (r4, r6);
    (r1, r3) <@ __shuffle4 (r1, r3);
    (r5, r7) <@ __shuffle4 (r5, r7);
    (r0, r1) <@ __shuffle2 (r0, r1);
    (r2, r3) <@ __shuffle2 (r2, r3);
    (r4, r5) <@ __shuffle2 (r4, r5);
    (r6, r7) <@ __shuffle2 (r6, r7);
    (r0, r4) <@ __shuffle1 (r0, r4);
    (r1, r5) <@ __shuffle1 (r1, r5);
    (r2, r6) <@ __shuffle1 (r2, r6);
    (r3, r7) <@ __shuffle1 (r3, r7);
    return (r0, r4, r1, r5, r2, r6, r3, r7);
  }
  
  proc _nttunpack (rp:W16.t Array256.t) : W16.t Array256.t = {
    
    var r0:W256.t;
    var r1:W256.t;
    var r2:W256.t;
    var r3:W256.t;
    var r4:W256.t;
    var r5:W256.t;
    var r6:W256.t;
    var r7:W256.t;
    
    r0 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 0));
    r1 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 1));
    r2 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 2));
    r3 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 3));
    r4 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 4));
    r5 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 5));
    r6 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 6));
    r7 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 7));
    (r0, r1, r2, r3, r4, r5, r6, r7) <@ __nttunpack128 (r0, r1, r2, r3, r4,
    r5, r6, r7);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 0) (r0)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 1) (r1)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 2) (r2)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 3) (r3)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 4) (r4)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 5) (r5)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 6) (r6)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 7) (r7)));
    r0 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 8));
    r1 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 9));
    r2 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 10));
    r3 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 11));
    r4 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 12));
    r5 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 13));
    r6 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 14));
    r7 <- (get256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 15));
    (r0, r1, r2, r3, r4, r5, r6, r7) <@ __nttunpack128 (r0, r1, r2, r3, r4,
    r5, r6, r7);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 8) (r0)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 9) (r1)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 10) (r2)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 11) (r3)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 12) (r4)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 13) (r5)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 14) (r6)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 15) (r7)));
    return (rp);
  }
  
  proc __csubq (r:W256.t, qx16:W256.t) : W256.t = {
    
    var t:W256.t;
    
    r <- VPSUB_16u16 r qx16;
    t <- VPSRA_16u16 r (W8.of_int 15);
    t <- VPAND_256 t qx16;
    r <- VPADD_16u16 t r;
    return (r);
  }
  
  proc __red16x (r:W256.t, qx16:W256.t, vx16:W256.t) : W256.t = {
    
    var x:W256.t;
    
    x <- VPMULH_16u16 r vx16;
    x <- VPSRA_16u16 x (W8.of_int 10);
    x <- VPMULL_16u16 x qx16;
    r <- VPSUB_16u16 r x;
    return (r);
  }
  
  proc __fqmulprecomp16x (b:W256.t, al:W256.t, ah:W256.t, qx16:W256.t) : 
  W256.t = {
    
    var x:W256.t;
    
    x <- VPMULL_16u16 al b;
    b <- VPMULH_16u16 ah b;
    x <- VPMULH_16u16 x qx16;
    b <- VPSUB_16u16 b x;
    return (b);
  }
  
  proc __fqmulx16 (a:W256.t, b:W256.t, qx16:W256.t, qinvx16:W256.t) : 
  W256.t = {
    
    var rd:W256.t;
    var rhi:W256.t;
    var rlo:W256.t;
    
    rhi <- VPMULH_16u16 a b;
    rlo <- VPMULL_16u16 a b;
    rlo <- VPMULL_16u16 rlo qinvx16;
    rlo <- VPMULH_16u16 rlo qx16;
    rd <- VPSUB_16u16 rhi rlo;
    return (rd);
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
      t <- ((invw b.[x1]) `&` b.[x2]);
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
    rC <- KECCAK1600_RC;
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
      (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => (state).[i_0])) (W64.to_uint i) ((
      (get8 (WArray200.init64 (fun i_0 => (state).[i_0])) (W64.to_uint i)) `^` c))));
      i <- (i + (W64.of_int 1));
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => (state).[i_0])) (W64.to_uint i) ((
    (get8 (WArray200.init64 (fun i_0 => (state).[i_0])) (W64.to_uint i)) `^` trail_byte))));
    i <- r8;
    i <- (i - (W64.of_int 1));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => (state).[i_0])) (W64.to_uint i) ((
    (get8 (WArray200.init64 (fun i_0 => (state).[i_0])) (W64.to_uint i)) `^` (W8.of_int 128)))));
    return (state);
  }
  
  proc _isha3_256 (out:W8.t Array32.t, in_0:W64.t, inlen:W64.t) : W8.t Array32.t = {
    var aux: int;
    
    var state:W64.t Array25.t;
    var r8:W64.t;
    var ilen:W64.t;
    var t8:W8.t;
    var i:int;
    var t64:W64.t;
    state <- witness;
    (* Erased call to spill *)
    state <@ __st0 (state);
    r8 <- (W64.of_int 136);
    ilen <- inlen;
    
    while ((r8 \ule ilen)) {
      (state, in_0, ilen) <@ __add_full_block (state, in_0, ilen, r8);
      (* Erased call to spill *)
      state <@ _keccakf1600_ (state);
      (* Erased call to unspill *)
    }
    t8 <- (W8.of_int 6);
    state <@ __add_final_block (state, in_0, ilen, t8, r8);
    state <@ _keccakf1600_ (state);
    (* Erased call to unspill *)
    i <- 0;
    while (i < 4) {
      t64 <- state.[i];
      out <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => (out).[i_0])) i (t64)));
      i <- i + 1;
    }
    return (out);
  }
  
  proc _shake256_1120_32 (out:W64.t, in0:W64.t, in1:W64.t) : unit = {
    var aux: int;
    
    var state:W64.t Array25.t;
    var i:int;
    var t64:W64.t;
    var r8:W64.t;
    var ilen:W64.t;
    var t8:W8.t;
    state <- witness;
    (* Erased call to spill *)
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
    (* Erased call to spill *)
    state <@ _keccakf1600_ (state);
    (* Erased call to unspill *)
    r8 <- (W64.of_int 136);
    ilen <- (W64.of_int (((3 * 320) + 128) - (136 - 32)));
    in1 <- (in1 + (W64.of_int (136 - 32)));
    
    while ((r8 \ule ilen)) {
      (state, in1, ilen) <@ __add_full_block (state, in1, ilen, r8);
      (* Erased call to spill *)
      state <@ _keccakf1600_ (state);
      (* Erased call to unspill *)
    }
    t8 <- (W8.of_int 31);
    state <@ __add_final_block (state, in1, ilen, t8, r8);
    state <@ _keccakf1600_ (state);
    (* Erased call to unspill *)
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
  
  proc _sha3_512_64 (out:W8.t Array64.t, in_0:W8.t Array64.t) : W8.t Array64.t = {
    var aux: int;
    
    var state:W64.t Array25.t;
    var i:int;
    var t64:W64.t;
    state <- witness;
    (* Erased call to spill *)
    state <@ __st0 (state);
    i <- 0;
    while (i < 8) {
      t64 <- (get64 (WArray64.init8 (fun i_0 => (in_0).[i_0])) i);
      state.[i] <- (state.[i] `^` t64);
      i <- i + 1;
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => (state).[i_0])) 64 ((
    (get8 (WArray200.init64 (fun i_0 => (state).[i_0])) 64) `^` (W8.of_int 6)))));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => (state).[i_0])) (72 - 1) ((
    (get8 (WArray200.init64 (fun i_0 => (state).[i_0])) (72 - 1)) `^` (W8.of_int 128)))));
    state <@ _keccakf1600_ (state);
    (* Erased call to unspill *)
    i <- 0;
    while (i < 8) {
      t64 <- state.[i];
      out <-
      Array64.init
      (WArray64.get8 (WArray64.set64 (WArray64.init8 (fun i_0 => (out).[i_0])) i (t64)));
      i <- i + 1;
    }
    return (out);
  }
  
  proc _sha3_512_32 (out:W8.t Array64.t, in_0:W8.t Array32.t) : W8.t Array64.t = {
    var aux: int;
    
    var state:W64.t Array25.t;
    var i:int;
    var t64:W64.t;
    state <- witness;
    (* Erased call to spill *)
    state <@ __st0 (state);
    i <- 0;
    while (i < 4) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => (in_0).[i_0])) i);
      state.[i] <- (state.[i] `^` t64);
      i <- i + 1;
    }
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => (state).[i_0])) 32 ((
    (get8 (WArray200.init64 (fun i_0 => (state).[i_0])) 32) `^` (W8.of_int 6)))));
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i_0 => (state).[i_0])) (72 - 1) ((
    (get8 (WArray200.init64 (fun i_0 => (state).[i_0])) (72 - 1)) `^` (W8.of_int 128)))));
    state <@ _keccakf1600_ (state);
    (* Erased call to unspill *)
    i <- 0;
    while (i < 8) {
      t64 <- state.[i];
      out <-
      Array64.init
      (WArray64.get8 (WArray64.set64 (WArray64.init8 (fun i_0 => (out).[i_0])) i (t64)));
      i <- i + 1;
    }
    return (out);
  }
  
  proc __rol_4u64_rho56 (a:W256.t) : W256.t = {
    
    var r:W256.t;
    
    r <- VPSHUFB_256 a rho56;
    return (r);
  }
  
  proc __rol_4u64_rho8 (a:W256.t) : W256.t = {
    
    var r:W256.t;
    
    r <- VPSHUFB_256 a rho8;
    return (r);
  }
  
  proc __rol_4u64 (a:W256.t, o:int) : W256.t = {
    
    var r:W256.t;
    var t256:W256.t;
    
    r <- VPSLL_4u64 a (W8.of_int o);
    t256 <- VPSRL_4u64 a (W8.of_int (64 - o));
    r <- (r `|` t256);
    return (r);
  }
  
  proc __prepare_theta (a_4x:W256.t Array25.t) : W256.t * W256.t * W256.t *
                                                 W256.t * W256.t = {
    
    var ca:W256.t;
    var ce:W256.t;
    var ci:W256.t;
    var co:W256.t;
    var cu:W256.t;
    
    ca <- a_4x.[20];
    ca <- (ca `^` a_4x.[15]);
    ca <- (ca `^` a_4x.[10]);
    ca <- (ca `^` a_4x.[5]);
    ca <- (ca `^` a_4x.[0]);
    ce <- a_4x.[21];
    ce <- (ce `^` a_4x.[16]);
    ce <- (ce `^` a_4x.[11]);
    ce <- (ce `^` a_4x.[6]);
    ce <- (ce `^` a_4x.[1]);
    ci <- a_4x.[22];
    ci <- (ci `^` a_4x.[17]);
    ci <- (ci `^` a_4x.[12]);
    ci <- (ci `^` a_4x.[7]);
    ci <- (ci `^` a_4x.[2]);
    co <- a_4x.[23];
    co <- (co `^` a_4x.[18]);
    co <- (co `^` a_4x.[13]);
    co <- (co `^` a_4x.[8]);
    co <- (co `^` a_4x.[3]);
    cu <- a_4x.[24];
    cu <- (cu `^` a_4x.[19]);
    cu <- (cu `^` a_4x.[14]);
    cu <- (cu `^` a_4x.[9]);
    cu <- (cu `^` a_4x.[4]);
    return (ca, ce, ci, co, cu);
  }
  
  proc __first (ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * W256.t = {
    
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    var ce1:W256.t;
    var ci1:W256.t;
    var co1:W256.t;
    var cu1:W256.t;
    var ca1:W256.t;
    
    ce1 <@ __rol_4u64 (ce, 1);
    da <- (cu `^` ce1);
    ci1 <@ __rol_4u64 (ci, 1);
    de <- (ca `^` ci1);
    co1 <@ __rol_4u64 (co, 1);
    di <- (ce `^` co1);
    cu1 <@ __rol_4u64 (cu, 1);
    do_0 <- (ci `^` cu1);
    ca1 <@ __rol_4u64 (ca, 1);
    du <- (co `^` ca1);
    return (da, de, di, do_0, du);
  }
  
  proc __second_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      index:int, ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t,
                      cu:W256.t, da:W256.t, de:W256.t, di:W256.t,
                      do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                W256.t Array25.t * W256.t *
                                                W256.t * W256.t * W256.t *
                                                W256.t = {
    
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    
    t256 <- a_4x.[0];
    t256 <- (t256 `^` da);
    a_4x.[0] <- t256;
    bba <- t256;
    t256 <- a_4x.[6];
    t256 <- (t256 `^` de);
    a_4x.[6] <- t256;
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- a_4x.[12];
    t256 <- (t256 `^` di);
    a_4x.[12] <- t256;
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- VPANDN_256 bbe bbi;
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` KeccakF1600RoundConstants.[index]);
    e_4x.[0] <- t256;
    ca <- t256;
    t256 <- a_4x.[18];
    t256 <- (t256 `^` do_0);
    a_4x.[18] <- t256;
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- VPANDN_256 bbi bbo;
    t256 <- (t256 `^` bbe);
    e_4x.[1] <- t256;
    ce <- t256;
    t256 <- a_4x.[24];
    t256 <- (t256 `^` du);
    a_4x.[24] <- t256;
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- VPANDN_256 bbo bbu;
    t256 <- (t256 `^` bbi);
    e_4x.[2] <- t256;
    ci <- t256;
    t256 <- VPANDN_256 bbu bba;
    t256 <- (t256 `^` bbo);
    e_4x.[3] <- t256;
    co <- t256;
    t256 <- VPANDN_256 bba bbe;
    t256 <- (t256 `^` bbu);
    e_4x.[4] <- t256;
    cu <- t256;
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __third_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    
    t256 <- a_4x.[3];
    t256 <- (t256 `^` do_0);
    a_4x.[3] <- t256;
    bga <@ __rol_4u64 (t256, 28);
    t256 <- a_4x.[9];
    t256 <- (t256 `^` du);
    a_4x.[9] <- t256;
    bge <@ __rol_4u64 (t256, 20);
    t256 <- a_4x.[10];
    t256 <- (t256 `^` da);
    a_4x.[10] <- t256;
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- VPANDN_256 bge bgi;
    t256 <- (t256 `^` bga);
    e_4x.[5] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[16];
    t256 <- (t256 `^` de);
    a_4x.[16] <- t256;
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- VPANDN_256 bgi bgo;
    t256 <- (t256 `^` bge);
    e_4x.[6] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[22];
    t256 <- (t256 `^` di);
    a_4x.[22] <- t256;
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- VPANDN_256 bgo bgu;
    t256 <- (t256 `^` bgi);
    e_4x.[7] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bgu bga;
    t256 <- (t256 `^` bgo);
    e_4x.[8] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bga bge;
    t256 <- (t256 `^` bgu);
    e_4x.[9] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __fourth_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t,
                      da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    
    t256 <- a_4x.[1];
    t256 <- (t256 `^` de);
    a_4x.[1] <- t256;
    bka <@ __rol_4u64 (t256, 1);
    t256 <- a_4x.[7];
    t256 <- (t256 `^` di);
    a_4x.[7] <- t256;
    bke <@ __rol_4u64 (t256, 6);
    t256 <- a_4x.[13];
    t256 <- (t256 `^` do_0);
    a_4x.[13] <- t256;
    bki <@ __rol_4u64 (t256, 25);
    t256 <- VPANDN_256 bke bki;
    t256 <- (t256 `^` bka);
    e_4x.[10] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[19];
    t256 <- (t256 `^` du);
    a_4x.[19] <- t256;
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- VPANDN_256 bki bko;
    t256 <- (t256 `^` bke);
    e_4x.[11] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[20];
    t256 <- (t256 `^` da);
    a_4x.[20] <- t256;
    bku <@ __rol_4u64 (t256, 18);
    t256 <- VPANDN_256 bko bku;
    t256 <- (t256 `^` bki);
    e_4x.[12] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bku bka;
    t256 <- (t256 `^` bko);
    e_4x.[13] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bka bke;
    t256 <- (t256 `^` bku);
    e_4x.[14] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __fifth_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    
    t256 <- a_4x.[4];
    t256 <- (t256 `^` du);
    a_4x.[4] <- t256;
    bma <@ __rol_4u64 (t256, 27);
    t256 <- a_4x.[5];
    t256 <- (t256 `^` da);
    a_4x.[5] <- t256;
    bme <@ __rol_4u64 (t256, 36);
    t256 <- a_4x.[11];
    t256 <- (t256 `^` de);
    a_4x.[11] <- t256;
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- VPANDN_256 bme bmi;
    t256 <- (t256 `^` bma);
    e_4x.[15] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[17];
    t256 <- (t256 `^` di);
    a_4x.[17] <- t256;
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- VPANDN_256 bmi bmo;
    t256 <- (t256 `^` bme);
    e_4x.[16] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[23];
    t256 <- (t256 `^` do_0);
    a_4x.[23] <- t256;
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- VPANDN_256 bmo bmu;
    t256 <- (t256 `^` bmi);
    e_4x.[17] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bmu bma;
    t256 <- (t256 `^` bmo);
    e_4x.[18] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bma bme;
    t256 <- (t256 `^` bmu);
    e_4x.[19] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __sixth_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    
    t256 <- a_4x.[2];
    t256 <- (t256 `^` di);
    a_4x.[2] <- t256;
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- a_4x.[8];
    t256 <- (t256 `^` do_0);
    a_4x.[8] <- t256;
    bse <@ __rol_4u64 (t256, 55);
    t256 <- a_4x.[14];
    t256 <- (t256 `^` du);
    a_4x.[14] <- t256;
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- VPANDN_256 bse bsi;
    t256 <- (t256 `^` bsa);
    e_4x.[20] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[15];
    t256 <- (t256 `^` da);
    a_4x.[15] <- t256;
    bso <@ __rol_4u64 (t256, 41);
    t256 <- VPANDN_256 bsi bso;
    t256 <- (t256 `^` bse);
    e_4x.[21] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[21];
    t256 <- (t256 `^` de);
    a_4x.[21] <- t256;
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- VPANDN_256 bso bsu;
    t256 <- (t256 `^` bsi);
    e_4x.[22] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bsu bsa;
    t256 <- (t256 `^` bso);
    e_4x.[23] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bsa bse;
    t256 <- (t256 `^` bsu);
    e_4x.[24] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __second_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, index:int,
                     ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t,
                     da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    
    t256 <- a_4x.[0];
    t256 <- (t256 `^` da);
    a_4x.[0] <- t256;
    bba <- t256;
    t256 <- a_4x.[6];
    t256 <- (t256 `^` de);
    a_4x.[6] <- t256;
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- a_4x.[12];
    t256 <- (t256 `^` di);
    a_4x.[12] <- t256;
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- VPANDN_256 bbe bbi;
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` KeccakF1600RoundConstants.[index]);
    e_4x.[0] <- t256;
    ca <- t256;
    t256 <- a_4x.[18];
    t256 <- (t256 `^` do_0);
    a_4x.[18] <- t256;
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- VPANDN_256 bbi bbo;
    t256 <- (t256 `^` bbe);
    e_4x.[1] <- t256;
    ce <- t256;
    t256 <- a_4x.[24];
    t256 <- (t256 `^` du);
    a_4x.[24] <- t256;
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- VPANDN_256 bbo bbu;
    t256 <- (t256 `^` bbi);
    e_4x.[2] <- t256;
    ci <- t256;
    t256 <- VPANDN_256 bbu bba;
    t256 <- (t256 `^` bbo);
    e_4x.[3] <- t256;
    co <- t256;
    t256 <- VPANDN_256 bba bbe;
    t256 <- (t256 `^` bbu);
    e_4x.[4] <- t256;
    cu <- t256;
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __third_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                    ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                    de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                                    W256.t Array25.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t = {
    
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    
    t256 <- a_4x.[3];
    t256 <- (t256 `^` do_0);
    a_4x.[3] <- t256;
    bga <@ __rol_4u64 (t256, 28);
    t256 <- a_4x.[9];
    t256 <- (t256 `^` du);
    a_4x.[9] <- t256;
    bge <@ __rol_4u64 (t256, 20);
    t256 <- a_4x.[10];
    t256 <- (t256 `^` da);
    a_4x.[10] <- t256;
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- VPANDN_256 bge bgi;
    t256 <- (t256 `^` bga);
    e_4x.[5] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[16];
    t256 <- (t256 `^` de);
    a_4x.[16] <- t256;
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- VPANDN_256 bgi bgo;
    t256 <- (t256 `^` bge);
    e_4x.[6] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[22];
    t256 <- (t256 `^` di);
    a_4x.[22] <- t256;
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- VPANDN_256 bgo bgu;
    t256 <- (t256 `^` bgi);
    e_4x.[7] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bgu bga;
    t256 <- (t256 `^` bgo);
    e_4x.[8] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bga bge;
    t256 <- (t256 `^` bgu);
    e_4x.[9] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __fourth_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    
    t256 <- a_4x.[1];
    t256 <- (t256 `^` de);
    a_4x.[1] <- t256;
    bka <@ __rol_4u64 (t256, 1);
    t256 <- a_4x.[7];
    t256 <- (t256 `^` di);
    a_4x.[7] <- t256;
    bke <@ __rol_4u64 (t256, 6);
    t256 <- a_4x.[13];
    t256 <- (t256 `^` do_0);
    a_4x.[13] <- t256;
    bki <@ __rol_4u64 (t256, 25);
    t256 <- VPANDN_256 bke bki;
    t256 <- (t256 `^` bka);
    e_4x.[10] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[19];
    t256 <- (t256 `^` du);
    a_4x.[19] <- t256;
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- VPANDN_256 bki bko;
    t256 <- (t256 `^` bke);
    e_4x.[11] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[20];
    t256 <- (t256 `^` da);
    a_4x.[20] <- t256;
    bku <@ __rol_4u64 (t256, 18);
    t256 <- VPANDN_256 bko bku;
    t256 <- (t256 `^` bki);
    e_4x.[12] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bku bka;
    t256 <- (t256 `^` bko);
    e_4x.[13] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bka bke;
    t256 <- (t256 `^` bku);
    e_4x.[14] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __fifth_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                    ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                    de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                                    W256.t Array25.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t = {
    
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    
    t256 <- a_4x.[4];
    t256 <- (t256 `^` du);
    a_4x.[4] <- t256;
    bma <@ __rol_4u64 (t256, 27);
    t256 <- a_4x.[5];
    t256 <- (t256 `^` da);
    a_4x.[5] <- t256;
    bme <@ __rol_4u64 (t256, 36);
    t256 <- a_4x.[11];
    t256 <- (t256 `^` de);
    a_4x.[11] <- t256;
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- VPANDN_256 bme bmi;
    t256 <- (t256 `^` bma);
    e_4x.[15] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[17];
    t256 <- (t256 `^` di);
    a_4x.[17] <- t256;
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- VPANDN_256 bmi bmo;
    t256 <- (t256 `^` bme);
    e_4x.[16] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[23];
    t256 <- (t256 `^` do_0);
    a_4x.[23] <- t256;
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- VPANDN_256 bmo bmu;
    t256 <- (t256 `^` bmi);
    e_4x.[17] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bmu bma;
    t256 <- (t256 `^` bmo);
    e_4x.[18] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bma bme;
    t256 <- (t256 `^` bmu);
    e_4x.[19] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __sixth_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                    ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                    de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                                    W256.t Array25.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t = {
    
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    
    t256 <- a_4x.[2];
    t256 <- (t256 `^` di);
    a_4x.[2] <- t256;
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- a_4x.[8];
    t256 <- (t256 `^` do_0);
    a_4x.[8] <- t256;
    bse <@ __rol_4u64 (t256, 55);
    t256 <- a_4x.[14];
    t256 <- (t256 `^` du);
    a_4x.[14] <- t256;
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- VPANDN_256 bse bsi;
    t256 <- (t256 `^` bsa);
    e_4x.[20] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[15];
    t256 <- (t256 `^` da);
    a_4x.[15] <- t256;
    bso <@ __rol_4u64 (t256, 41);
    t256 <- VPANDN_256 bsi bso;
    t256 <- (t256 `^` bse);
    e_4x.[21] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[21];
    t256 <- (t256 `^` de);
    a_4x.[21] <- t256;
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- VPANDN_256 bso bsu;
    t256 <- (t256 `^` bsi);
    e_4x.[22] <- t256;
    ci <- (ci `^` t256);
    t256 <- VPANDN_256 bsu bsa;
    t256 <- (t256 `^` bso);
    e_4x.[23] <- t256;
    co <- (co `^` t256);
    t256 <- VPANDN_256 bsa bse;
    t256 <- (t256 `^` bsu);
    e_4x.[24] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __second_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      index:int, da:W256.t, de:W256.t, di:W256.t,
                      do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                W256.t Array25.t = {
    
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    
    t256 <- a_4x.[0];
    t256 <- (t256 `^` da);
    a_4x.[0] <- t256;
    bba <- t256;
    t256 <- a_4x.[6];
    t256 <- (t256 `^` de);
    a_4x.[6] <- t256;
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- a_4x.[12];
    t256 <- (t256 `^` di);
    a_4x.[12] <- t256;
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- VPANDN_256 bbe bbi;
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` KeccakF1600RoundConstants.[index]);
    e_4x.[0] <- t256;
    t256 <- a_4x.[18];
    t256 <- (t256 `^` do_0);
    a_4x.[18] <- t256;
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- VPANDN_256 bbi bbo;
    t256 <- (t256 `^` bbe);
    e_4x.[1] <- t256;
    t256 <- a_4x.[24];
    t256 <- (t256 `^` du);
    a_4x.[24] <- t256;
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- VPANDN_256 bbo bbu;
    t256 <- (t256 `^` bbi);
    e_4x.[2] <- t256;
    t256 <- VPANDN_256 bbu bba;
    t256 <- (t256 `^` bbo);
    e_4x.[3] <- t256;
    t256 <- VPANDN_256 bba bbe;
    t256 <- (t256 `^` bbu);
    e_4x.[4] <- t256;
    return (a_4x, e_4x);
  }
  
  proc __third_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    
    t256 <- a_4x.[3];
    t256 <- (t256 `^` do_0);
    a_4x.[3] <- t256;
    bga <@ __rol_4u64 (t256, 28);
    t256 <- a_4x.[9];
    t256 <- (t256 `^` du);
    a_4x.[9] <- t256;
    bge <@ __rol_4u64 (t256, 20);
    t256 <- a_4x.[10];
    t256 <- (t256 `^` da);
    a_4x.[10] <- t256;
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- VPANDN_256 bge bgi;
    t256 <- (t256 `^` bga);
    e_4x.[5] <- t256;
    t256 <- a_4x.[16];
    t256 <- (t256 `^` de);
    a_4x.[16] <- t256;
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- VPANDN_256 bgi bgo;
    t256 <- (t256 `^` bge);
    e_4x.[6] <- t256;
    t256 <- a_4x.[22];
    t256 <- (t256 `^` di);
    a_4x.[22] <- t256;
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- VPANDN_256 bgo bgu;
    t256 <- (t256 `^` bgi);
    e_4x.[7] <- t256;
    t256 <- VPANDN_256 bgu bga;
    t256 <- (t256 `^` bgo);
    e_4x.[8] <- t256;
    t256 <- VPANDN_256 bga bge;
    t256 <- (t256 `^` bgu);
    e_4x.[9] <- t256;
    return (a_4x, e_4x);
  }
  
  proc __fourth_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    
    t256 <- a_4x.[1];
    t256 <- (t256 `^` de);
    a_4x.[1] <- t256;
    bka <@ __rol_4u64 (t256, 1);
    t256 <- a_4x.[7];
    t256 <- (t256 `^` di);
    a_4x.[7] <- t256;
    bke <@ __rol_4u64 (t256, 6);
    t256 <- a_4x.[13];
    t256 <- (t256 `^` do_0);
    a_4x.[13] <- t256;
    bki <@ __rol_4u64 (t256, 25);
    t256 <- VPANDN_256 bke bki;
    t256 <- (t256 `^` bka);
    e_4x.[10] <- t256;
    t256 <- a_4x.[19];
    t256 <- (t256 `^` du);
    a_4x.[19] <- t256;
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- VPANDN_256 bki bko;
    t256 <- (t256 `^` bke);
    e_4x.[11] <- t256;
    t256 <- a_4x.[20];
    t256 <- (t256 `^` da);
    a_4x.[20] <- t256;
    bku <@ __rol_4u64 (t256, 18);
    t256 <- VPANDN_256 bko bku;
    t256 <- (t256 `^` bki);
    e_4x.[12] <- t256;
    t256 <- VPANDN_256 bku bka;
    t256 <- (t256 `^` bko);
    e_4x.[13] <- t256;
    t256 <- VPANDN_256 bka bke;
    t256 <- (t256 `^` bku);
    e_4x.[14] <- t256;
    return (a_4x, e_4x);
  }
  
  proc __fifth_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    
    t256 <- a_4x.[4];
    t256 <- (t256 `^` du);
    a_4x.[4] <- t256;
    bma <@ __rol_4u64 (t256, 27);
    t256 <- a_4x.[5];
    t256 <- (t256 `^` da);
    a_4x.[5] <- t256;
    bme <@ __rol_4u64 (t256, 36);
    t256 <- a_4x.[11];
    t256 <- (t256 `^` de);
    a_4x.[11] <- t256;
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- VPANDN_256 bme bmi;
    t256 <- (t256 `^` bma);
    e_4x.[15] <- t256;
    t256 <- a_4x.[17];
    t256 <- (t256 `^` di);
    a_4x.[17] <- t256;
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- VPANDN_256 bmi bmo;
    t256 <- (t256 `^` bme);
    e_4x.[16] <- t256;
    t256 <- a_4x.[23];
    t256 <- (t256 `^` do_0);
    a_4x.[23] <- t256;
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- VPANDN_256 bmo bmu;
    t256 <- (t256 `^` bmi);
    e_4x.[17] <- t256;
    t256 <- VPANDN_256 bmu bma;
    t256 <- (t256 `^` bmo);
    e_4x.[18] <- t256;
    t256 <- VPANDN_256 bma bme;
    t256 <- (t256 `^` bmu);
    e_4x.[19] <- t256;
    return (a_4x, e_4x);
  }
  
  proc __sixth_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    
    t256 <- a_4x.[2];
    t256 <- (t256 `^` di);
    a_4x.[2] <- t256;
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- a_4x.[8];
    t256 <- (t256 `^` do_0);
    a_4x.[8] <- t256;
    bse <@ __rol_4u64 (t256, 55);
    t256 <- a_4x.[14];
    t256 <- (t256 `^` du);
    a_4x.[14] <- t256;
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- VPANDN_256 bse bsi;
    t256 <- (t256 `^` bsa);
    e_4x.[20] <- t256;
    t256 <- a_4x.[15];
    t256 <- (t256 `^` da);
    a_4x.[15] <- t256;
    bso <@ __rol_4u64 (t256, 41);
    t256 <- VPANDN_256 bsi bso;
    t256 <- (t256 `^` bse);
    e_4x.[21] <- t256;
    t256 <- a_4x.[21];
    t256 <- (t256 `^` de);
    a_4x.[21] <- t256;
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- VPANDN_256 bso bsu;
    t256 <- (t256 `^` bsi);
    e_4x.[22] <- t256;
    t256 <- VPANDN_256 bsu bsa;
    t256 <- (t256 `^` bso);
    e_4x.[23] <- t256;
    t256 <- VPANDN_256 bsa bse;
    t256 <- (t256 `^` bsu);
    e_4x.[24] <- t256;
    return (a_4x, e_4x);
  }
  
  proc __theta_rho_pi_chi_iota_prepare_theta_even (a_4x:W256.t Array25.t,
                                                   e_4x:W256.t Array25.t,
                                                   index:int, ca:W256.t,
                                                   ce:W256.t, ci:W256.t,
                                                   co:W256.t, cu:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __second_even (a_4x, e_4x, index, ca,
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __third_even (a_4x, e_4x, ca, ce, ci,
    co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fourth_even (a_4x, e_4x, ca, ce,
    ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fifth_even (a_4x, e_4x, ca, ce, ci,
    co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __sixth_even (a_4x, e_4x, ca, ce, ci,
    co, cu, da, de, di, do_0, du);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __theta_rho_pi_chi_iota_prepare_theta_odd (a_4x:W256.t Array25.t,
                                                  e_4x:W256.t Array25.t,
                                                  index:int, ca:W256.t,
                                                  ce:W256.t, ci:W256.t,
                                                  co:W256.t, cu:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __second_odd (a_4x, e_4x, index, ca,
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __third_odd (a_4x, e_4x, ca, ce, ci,
    co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fourth_odd (a_4x, e_4x, ca, ce, ci,
    co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fifth_odd (a_4x, e_4x, ca, ce, ci,
    co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __sixth_odd (a_4x, e_4x, ca, ce, ci,
    co, cu, da, de, di, do_0, du);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  
  proc __theta_rho_pi_chi_iota (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                                index:int, ca:W256.t, ce:W256.t, ci:W256.t,
                                co:W256.t, cu:W256.t) : W256.t Array25.t *
                                                        W256.t Array25.t = {
    
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x) <@ __second_last (a_4x, e_4x, index, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __third_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __fourth_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __fifth_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __sixth_last (a_4x, e_4x, da, de, di, do_0, du);
    return (a_4x, e_4x);
  }
  
  proc _KeccakF1600_StatePermute4x (a_4x:W256.t Array25.t) : W256.t Array25.t = {
    
    var ca:W256.t;
    var ce:W256.t;
    var ci:W256.t;
    var co:W256.t;
    var cu:W256.t;
    var e_4x:W256.t Array25.t;
    e_4x <- witness;
    (ca, ce, ci, co, cu) <@ __prepare_theta (a_4x);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 0, ca, ce,
    ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 1, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 2, ca, ce,
    ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 3, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 4, ca, ce,
    ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 5, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 6, ca, ce,
    ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 7, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 8, ca, ce,
    ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 9, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 10, ca,
    ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 11, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 12, ca,
    ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 13, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 14, ca,
    ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 15, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 16, ca,
    ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 17, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 18, ca,
    ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 19, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 20, ca,
    ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (e_4x, a_4x, 21, ca, ce,
    ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co,
    cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (a_4x, e_4x, 22, ca,
    ce, ci, co, cu);
    (e_4x, a_4x) <@ __theta_rho_pi_chi_iota (e_4x, a_4x, 23, ca, ce, ci, co,
    cu);
    return (a_4x);
  }
  
  proc _shake256_absorb4x_33 (s:W256.t Array25.t, m0:W8.t Array33.t,
                              m1:W8.t Array33.t, m2:W8.t Array33.t,
                              m3:W8.t Array33.t) : W256.t Array25.t = {
    var aux: int;
    
    var t0:W256.t;
    var i:int;
    var t64:W64.t;
    var t8:W8.t;
    var t1:W256.t;
    
    i <- 0;
    while (i < 25) {
      t0 <- set0_256 ;
      s.[i] <- t0;
      i <- i + 1;
    }
    i <- 0;
    while (i < 4) {
      t64 <- (get64 (WArray33.init8 (fun i_0 => (m0).[i_0])) i);
      s <-
      Array25.init
      (WArray800.get256 (WArray800.set64 (WArray800.init256 (fun i_0 => (s).[i_0])) (4 * i) ((
      (get64 (WArray800.init256 (fun i_0 => (s).[i_0])) (4 * i)) `^` t64))));
      t64 <- (get64 (WArray33.init8 (fun i_0 => (m1).[i_0])) i);
      s <-
      Array25.init
      (WArray800.get256 (WArray800.set64 (WArray800.init256 (fun i_0 => (s).[i_0])) ((4 * i) + 1) ((
      (get64 (WArray800.init256 (fun i_0 => (s).[i_0])) ((4 * i) + 1)) `^` t64))));
      t64 <- (get64 (WArray33.init8 (fun i_0 => (m2).[i_0])) i);
      s <-
      Array25.init
      (WArray800.get256 (WArray800.set64 (WArray800.init256 (fun i_0 => (s).[i_0])) ((4 * i) + 2) ((
      (get64 (WArray800.init256 (fun i_0 => (s).[i_0])) ((4 * i) + 2)) `^` t64))));
      t64 <- (get64 (WArray33.init8 (fun i_0 => (m3).[i_0])) i);
      s <-
      Array25.init
      (WArray800.get256 (WArray800.set64 (WArray800.init256 (fun i_0 => (s).[i_0])) ((4 * i) + 3) ((
      (get64 (WArray800.init256 (fun i_0 => (s).[i_0])) ((4 * i) + 3)) `^` t64))));
      i <- i + 1;
    }
    t8 <- m0.[32];
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 128 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 128) `^` t8))));
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 129 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 129) `^` (W8.of_int 31)))));
    t8 <- m1.[32];
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 136 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 136) `^` t8))));
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 137 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 137) `^` (W8.of_int 31)))));
    t8 <- m2.[32];
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 144 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 144) `^` t8))));
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 145 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 145) `^` (W8.of_int 31)))));
    t8 <- m3.[32];
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 152 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 152) `^` t8))));
    s <-
    Array25.init
    (WArray800.get256 (WArray800.set8 (WArray800.init256 (fun i_0 => (s).[i_0])) 153 ((
    (get8 (WArray800.init256 (fun i_0 => (s).[i_0])) 153) `^` (W8.of_int 31)))));
    t0 <- (get256 (WArray32.init64 (fun i_0 => (shake_sep).[i_0])) 0);
    t1 <- s.[((136 %/ 8) - 1)];
    t0 <- (t0 `^` t1);
    s.[((136 %/ 8) - 1)] <- t0;
    return (s);
  }
  
  proc __shake256_squeezeblock4x (state:W256.t Array25.t, h0:W8.t Array136.t,
                                  h1:W8.t Array136.t, h2:W8.t Array136.t,
                                  h3:W8.t Array136.t) : W256.t Array25.t *
                                                        W8.t Array136.t *
                                                        W8.t Array136.t *
                                                        W8.t Array136.t *
                                                        W8.t Array136.t = {
    var aux: int;
    
    var i:int;
    var t256:W256.t;
    var t128:W128.t;
    
    state <@ _KeccakF1600_StatePermute4x (state);
    aux <- (136 %/ 8);
    i <- 0;
    while (i < aux) {
      t256 <- state.[i];
      t128 <- (truncateu128 t256);
      h0 <-
      Array136.init
      (WArray136.get8 (WArray136.set64 (WArray136.init8 (fun i_0 => (h0).[i_0])) i (VMOVLPD t128)));
      h1 <-
      Array136.init
      (WArray136.get8 (WArray136.set64 (WArray136.init8 (fun i_0 => (h1).[i_0])) i (VMOVHPD t128)));
      t128 <- VEXTRACTI128 t256 (W8.of_int 1);
      h2 <-
      Array136.init
      (WArray136.get8 (WArray136.set64 (WArray136.init8 (fun i_0 => (h2).[i_0])) i (VMOVLPD t128)));
      h3 <-
      Array136.init
      (WArray136.get8 (WArray136.set64 (WArray136.init8 (fun i_0 => (h3).[i_0])) i (VMOVHPD t128)));
      i <- i + 1;
    }
    return (state, h0, h1, h2, h3);
  }
  
  proc _poly_add2 (rp:W16.t Array256.t, bp:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var i:int;
    var a:W256.t;
    var b:W256.t;
    var r:W256.t;
    
    i <- 0;
    while (i < 16) {
      a <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * i));
      b <-
      (get256_direct (WArray512.init16 (fun i_0 => (bp).[i_0])) (32 * i));
      r <- VPADD_16u16 a b;
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * i) (r)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_csubq (rp:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var qx16:W256.t;
    var i:int;
    var r:W256.t;
    
    qx16 <- (get256 (WArray32.init16 (fun i_0 => (jqx16).[i_0])) 0);
    i <- 0;
    while (i < 16) {
      r <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * i));
      r <@ __csubq (r, qx16);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * i) (r)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc __w256_interleave_u16 (al:W256.t, ah:W256.t) : W256.t * W256.t = {
    
    var a0:W256.t;
    var a1:W256.t;
    
    a0 <- VPUNPCKL_16u16 al ah;
    a1 <- VPUNPCKH_16u16 al ah;
    return (a0, a1);
  }
  
  proc __w256_deinterleave_u16 (_zero:W256.t, a0:W256.t, a1:W256.t) : 
  W256.t * W256.t = {
    
    var al:W256.t;
    var ah:W256.t;
    
    al <- VPBLEND_16u16 a0 _zero (W8.of_int 170);
    ah <- VPBLEND_16u16 a1 _zero (W8.of_int 170);
    al <- VPACKUS_8u32 al ah;
    a0 <- VPSRL_8u32 a0 (W8.of_int 16);
    a1 <- VPSRL_8u32 a1 (W8.of_int 16);
    ah <- VPACKUS_8u32 a0 a1;
    return (al, ah);
  }
  
  proc __mont_red (lo:W256.t, hi:W256.t, qx16:W256.t, qinvx16:W256.t) : 
  W256.t = {
    
    var m:W256.t;
    
    m <- VPMULL_16u16 lo qinvx16;
    m <- VPMULH_16u16 m qx16;
    lo <- VPSUB_16u16 hi m;
    return (lo);
  }
  
  proc __wmul_16u16 (x:W256.t, y:W256.t) : W256.t * W256.t = {
    
    var xy0:W256.t;
    var xy1:W256.t;
    var xyL:W256.t;
    var xyH:W256.t;
    
    xyL <- VPMULL_16u16 x y;
    xyH <- VPMULH_16u16 x y;
    (xy0, xy1) <@ __w256_interleave_u16 (xyL, xyH);
    return (xy0, xy1);
  }
  
  proc __schoolbook16x (are:W256.t, aim:W256.t, bre:W256.t, bim:W256.t,
                        zeta_0:W256.t, zetaqinv:W256.t, qx16:W256.t,
                        qinvx16:W256.t, sign:int) : W256.t * W256.t = {
    
    var x0:W256.t;
    var y0:W256.t;
    var zaim:W256.t;
    var ac0:W256.t;
    var ac1:W256.t;
    var ad0:W256.t;
    var ad1:W256.t;
    var bc0:W256.t;
    var bc1:W256.t;
    var zbd0:W256.t;
    var zbd1:W256.t;
    var x1:W256.t;
    var y1:W256.t;
    var _zero:W256.t;
    
    zaim <@ __fqmulprecomp16x (aim, zetaqinv, zeta_0, qx16);
    (ac0, ac1) <@ __wmul_16u16 (are, bre);
    (ad0, ad1) <@ __wmul_16u16 (are, bim);
    (bc0, bc1) <@ __wmul_16u16 (aim, bre);
    (zbd0, zbd1) <@ __wmul_16u16 (zaim, bim);
    if ((sign = 0)) {
      x0 <- VPADD_8u32 ac0 zbd0;
      x1 <- VPADD_8u32 ac1 zbd1;
    } else {
      x0 <- VPSUB_8u32 ac0 zbd0;
      x1 <- VPSUB_8u32 ac1 zbd1;
    }
    y0 <- VPADD_8u32 bc0 ad0;
    y1 <- VPADD_8u32 bc1 ad1;
    _zero <- set0_256 ;
    (x0, x1) <@ __w256_deinterleave_u16 (_zero, x0, x1);
    (y0, y1) <@ __w256_deinterleave_u16 (_zero, y0, y1);
    x0 <@ __mont_red (x0, x1, qx16, qinvx16);
    y0 <@ __mont_red (y0, y1, qx16, qinvx16);
    return (x0, y0);
  }
  
  proc _poly_basemul (rp:W16.t Array256.t, ap:W16.t Array256.t,
                      bp:W16.t Array256.t) : W16.t Array256.t = {
    
    var qx16:W256.t;
    var qinvx16:W256.t;
    var zetaqinv:W256.t;
    var zeta_0:W256.t;
    var are:W256.t;
    var aim:W256.t;
    var bre:W256.t;
    var bim:W256.t;
    
    qx16 <- (get256_direct (WArray32.init16 (fun i => (jqx16).[i])) 0);
    qinvx16 <- (get256_direct (WArray32.init16 (fun i => (jqinvx16).[i])) 0);
    zetaqinv <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 272);
    zeta_0 <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 304);
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 0));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 1));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 0));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 1));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 0);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 0) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 1) (aim)));
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 2));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 3));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 2));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 3));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 1);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 2) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 3) (aim)));
    zetaqinv <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 336);
    zeta_0 <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 368);
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 4));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 5));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 4));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 5));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 0);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 4) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 5) (aim)));
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 6));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 7));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 6));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 7));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 1);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 6) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 7) (aim)));
    zetaqinv <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 664);
    zeta_0 <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 696);
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 8));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 9));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 8));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 9));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 0);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 8) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 9) (aim)));
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 10));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 11));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 10));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 11));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 1);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 10) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 11) (aim)));
    zetaqinv <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 728);
    zeta_0 <-
    (get256_direct (WArray800.init16 (fun i => (jzetas_exp).[i])) 760);
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 12));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 13));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 12));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 13));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 0);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 12) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 13) (aim)));
    are <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 14));
    aim <- (get256_direct (WArray512.init16 (fun i => (ap).[i])) (32 * 15));
    bre <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 14));
    bim <- (get256_direct (WArray512.init16 (fun i => (bp).[i])) (32 * 15));
    (are, aim) <@ __schoolbook16x (are, aim, bre, bim, zeta_0, zetaqinv,
    qx16, qinvx16, 1);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 14) (are)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i => (rp).[i])) (32 * 15) (aim)));
    return (rp);
  }
  
  proc _poly_compress (rp:W64.t, a:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var x16p:W16.t Array16.t;
    var v:W256.t;
    var shift1:W256.t;
    var mask:W256.t;
    var shift2:W256.t;
    var permidx:W256.t;
    var i:int;
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var f3:W256.t;
    x16p <- witness;
    a <@ _poly_csubq (a);
    x16p <- jvx16;
    v <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    shift1 <- VPBROADCAST_16u16 pc_shift1_s;
    mask <- VPBROADCAST_16u16 pc_mask_s;
    shift2 <- VPBROADCAST_16u16 pc_shift2_s;
    permidx <-
    (get256 (WArray32.init32 (fun i_0 => (pc_permidx_s).[i_0])) 0);
    aux <- (256 %/ 64);
    i <- 0;
    while (i < aux) {
      f0 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) (4 * i));
      f1 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((4 * i) + 1));
      f2 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((4 * i) + 2));
      f3 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((4 * i) + 3));
      f0 <- VPMULH_16u16 f0 v;
      f1 <- VPMULH_16u16 f1 v;
      f2 <- VPMULH_16u16 f2 v;
      f3 <- VPMULH_16u16 f3 v;
      f0 <- VPMULHRS_16u16 f0 shift1;
      f1 <- VPMULHRS_16u16 f1 shift1;
      f2 <- VPMULHRS_16u16 f2 shift1;
      f3 <- VPMULHRS_16u16 f3 shift1;
      f0 <- VPAND_256 f0 mask;
      f1 <- VPAND_256 f1 mask;
      f2 <- VPAND_256 f2 mask;
      f3 <- VPAND_256 f3 mask;
      f0 <- VPACKUS_16u16 f0 f1;
      f2 <- VPACKUS_16u16 f2 f3;
      f0 <- VPMADDUBSW_256 f0 shift2;
      f2 <- VPMADDUBSW_256 f2 shift2;
      f0 <- VPACKUS_16u16 f0 f2;
      f0 <- VPERMD permidx f0;
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int (32 * i)))) (f0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc _poly_compress_1 (rp:W8.t Array128.t, a:W16.t Array256.t) : W8.t Array128.t *
                                                                   W16.t Array256.t = {
    var aux: int;
    
    var x16p:W16.t Array16.t;
    var v:W256.t;
    var shift1:W256.t;
    var mask:W256.t;
    var shift2:W256.t;
    var permidx:W256.t;
    var i:int;
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var f3:W256.t;
    x16p <- witness;
    a <@ _poly_csubq (a);
    x16p <- jvx16;
    v <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    shift1 <- VPBROADCAST_16u16 pc_shift1_s;
    mask <- VPBROADCAST_16u16 pc_mask_s;
    shift2 <- VPBROADCAST_16u16 pc_shift2_s;
    permidx <-
    (get256 (WArray32.init32 (fun i_0 => (pc_permidx_s).[i_0])) 0);
    aux <- (256 %/ 64);
    i <- 0;
    while (i < aux) {
      f0 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) (4 * i));
      f1 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((4 * i) + 1));
      f2 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((4 * i) + 2));
      f3 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((4 * i) + 3));
      f0 <- VPMULH_16u16 f0 v;
      f1 <- VPMULH_16u16 f1 v;
      f2 <- VPMULH_16u16 f2 v;
      f3 <- VPMULH_16u16 f3 v;
      f0 <- VPMULHRS_16u16 f0 shift1;
      f1 <- VPMULHRS_16u16 f1 shift1;
      f2 <- VPMULHRS_16u16 f2 shift1;
      f3 <- VPMULHRS_16u16 f3 shift1;
      f0 <- VPAND_256 f0 mask;
      f1 <- VPAND_256 f1 mask;
      f2 <- VPAND_256 f2 mask;
      f3 <- VPAND_256 f3 mask;
      f0 <- VPACKUS_16u16 f0 f1;
      f2 <- VPACKUS_16u16 f2 f3;
      f0 <- VPMADDUBSW_256 f0 shift2;
      f2 <- VPMADDUBSW_256 f2 shift2;
      f0 <- VPACKUS_16u16 f0 f2;
      f0 <- VPERMD permidx f0;
      rp <-
      Array128.init
      (WArray128.get8 (WArray128.set256_direct (WArray128.init8 (fun i_0 => (rp).[i_0])) (32 * i) (f0)));
      i <- i + 1;
    }
    return (rp, a);
  }
  
  proc _poly_decompress (rp:W16.t Array256.t, ap:W64.t) : W16.t Array256.t = {
    var aux: int;
    
    var x16p:W16.t Array16.t;
    var q:W256.t;
    var x32p:W8.t Array32.t;
    var shufbidx:W256.t;
    var mask:W256.t;
    var shift:W256.t;
    var f:W256.t;
    var i:int;
    var h:W128.t;
    var sh:W128.t;
    x16p <- witness;
    x32p <- witness;
    x16p <- jqx16;
    q <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    x32p <- pd_jshufbidx;
    shufbidx <- (get256 (WArray32.init8 (fun i_0 => (x32p).[i_0])) 0);
    mask <- VPBROADCAST_8u32 pd_mask_s;
    shift <- VPBROADCAST_8u32 pd_shift_s;
    f <- set0_256 ;
    aux <- (256 %/ 16);
    i <- 0;
    while (i < aux) {
      h <-
      (zeroextu128 (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i))))));
      sh <- h;
      f <- VPBROADCAST_2u128 sh;
      f <- VPSHUFB_256 f shufbidx;
      f <- VPAND_256 f mask;
      f <- VPMULL_16u16 f shift;
      f <- VPMULHRS_16u16 f q;
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) i (f)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_frombytes (rp:W16.t Array256.t, ap:W64.t) : W16.t Array256.t = {
    var aux: int;
    
    var maskp:W16.t Array16.t;
    var mask:W256.t;
    var i:int;
    var t0:W256.t;
    var t1:W256.t;
    var t2:W256.t;
    var t3:W256.t;
    var t4:W256.t;
    var t5:W256.t;
    var tt:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    var t8:W256.t;
    var t9:W256.t;
    var t10:W256.t;
    var t11:W256.t;
    maskp <- witness;
    maskp <- maskx16;
    mask <- (get256 (WArray32.init16 (fun i_0 => (maskp).[i_0])) 0);
    i <- 0;
    while (i < 2) {
      t0 <- (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int (192 * i)))));
      t1 <-
      (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int ((192 * i) + 32)))));
      t2 <-
      (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int ((192 * i) + 64)))));
      t3 <-
      (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int ((192 * i) + 96)))));
      t4 <-
      (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int ((192 * i) + 128)))));
      t5 <-
      (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int ((192 * i) + 160)))));
      (tt, t3) <@ __shuffle8 (t0, t3);
      (t0, t4) <@ __shuffle8 (t1, t4);
      (t1, t5) <@ __shuffle8 (t2, t5);
      (t2, t4) <@ __shuffle4 (tt, t4);
      (tt, t1) <@ __shuffle4 (t3, t1);
      (t3, t5) <@ __shuffle4 (t0, t5);
      (t0, t1) <@ __shuffle2 (t2, t1);
      (t2, t3) <@ __shuffle2 (t4, t3);
      (t4, t5) <@ __shuffle2 (tt, t5);
      (t6, t3) <@ __shuffle1 (t0, t3);
      (t0, t4) <@ __shuffle1 (t1, t4);
      (t1, t5) <@ __shuffle1 (t2, t5);
      t7 <- VPSRL_16u16 t6 (W8.of_int 12);
      t8 <- VPSLL_16u16 t3 (W8.of_int 4);
      t7 <- VPOR_256 t7 t8;
      t6 <- VPAND_256 mask t6;
      t7 <- VPAND_256 mask t7;
      t8 <- VPSRL_16u16 t3 (W8.of_int 8);
      t9 <- VPSLL_16u16 t0 (W8.of_int 8);
      t8 <- VPOR_256 t8 t9;
      t8 <- VPAND_256 mask t8;
      t9 <- VPSRL_16u16 t0 (W8.of_int 4);
      t9 <- VPAND_256 mask t9;
      t10 <- VPSRL_16u16 t4 (W8.of_int 12);
      t11 <- VPSLL_16u16 t1 (W8.of_int 4);
      t10 <- VPOR_256 t10 t11;
      t4 <- VPAND_256 mask t4;
      t10 <- VPAND_256 mask t10;
      t11 <- VPSRL_16u16 t1 (W8.of_int 8);
      tt <- VPSLL_16u16 t5 (W8.of_int 8);
      t11 <- VPOR_256 t11 tt;
      t11 <- VPAND_256 mask t11;
      tt <- VPSRL_16u16 t5 (W8.of_int 4);
      tt <- VPAND_256 mask tt;
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) (8 * i) (t6)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((8 * i) + 1) (t7)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((8 * i) + 2) (t8)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((8 * i) + 3) (t9)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((8 * i) + 4) (t4)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((8 * i) + 5) (t10)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((8 * i) + 6) (t11)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((8 * i) + 7) (tt)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_frommont (rp:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var x16p:W16.t Array16.t;
    var qx16:W256.t;
    var qinvx16:W256.t;
    var dmontx16:W256.t;
    var i:int;
    var t:W256.t;
    x16p <- witness;
    x16p <- jqx16;
    qx16 <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    x16p <- jqinvx16;
    qinvx16 <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    x16p <- jdmontx16;
    dmontx16 <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    aux <- (256 %/ 16);
    i <- 0;
    while (i < aux) {
      t <- (get256 (WArray512.init16 (fun i_0 => (rp).[i_0])) i);
      t <@ __fqmulx16 (t, dmontx16, qx16, qinvx16);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) i (t)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_frommsg_1 (rp:W16.t Array256.t, ap:W8.t Array32.t) : W16.t Array256.t = {
    var aux: int;
    
    var x16p:W16.t Array16.t;
    var hqs:W256.t;
    var shift:W256.t;
    var idx:W256.t;
    var f:W256.t;
    var i:int;
    var g3:W256.t;
    var g0:W256.t;
    var g1:W256.t;
    var g2:W256.t;
    var h0:W256.t;
    var h2:W256.t;
    var h1:W256.t;
    var h3:W256.t;
    x16p <- witness;
    x16p <- hqx16_p1;
    hqs <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    shift <-
    VPBROADCAST_2u128 (get128
                      (WArray16.init32 (fun i_0 => (pfm_shift_s).[i_0])) 0);
    idx <-
    VPBROADCAST_2u128 (get128 (WArray16.init8 (fun i_0 => (pfm_idx_s).[i_0]))
                      0);
    f <- (get256 (WArray32.init8 (fun i_0 => (ap).[i_0])) 0);
    i <- 0;
    while (i < 4) {
      g3 <- VPSHUFD_256 f (W8.of_int (85 * i));
      g3 <- VPSLLV_8u32 g3 shift;
      g3 <- VPSHUFB_256 g3 idx;
      g0 <- VPSLL_16u16 g3 (W8.of_int 12);
      g1 <- VPSLL_16u16 g3 (W8.of_int 8);
      g2 <- VPSLL_16u16 g3 (W8.of_int 4);
      g0 <- VPSRA_16u16 g0 (W8.of_int 15);
      g1 <- VPSRA_16u16 g1 (W8.of_int 15);
      g2 <- VPSRA_16u16 g2 (W8.of_int 15);
      g3 <- VPSRA_16u16 g3 (W8.of_int 15);
      g0 <- VPAND_256 g0 hqs;
      g1 <- VPAND_256 g1 hqs;
      g2 <- VPAND_256 g2 hqs;
      g3 <- VPAND_256 g3 hqs;
      h0 <- VPUNPCKL_4u64 g0 g1;
      h2 <- VPUNPCKH_4u64 g0 g1;
      h1 <- VPUNPCKL_4u64 g2 g3;
      h3 <- VPUNPCKH_4u64 g2 g3;
      g0 <- VPERM2I128 h0 h1 (W8.of_int 32);
      g2 <- VPERM2I128 h0 h1 (W8.of_int 49);
      g1 <- VPERM2I128 h2 h3 (W8.of_int 32);
      g3 <- VPERM2I128 h2 h3 (W8.of_int 49);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) (2 * i) (g0)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((2 * i) + 1) (g1)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((2 * i) + 8) (g2)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) (((2 * i) + 8) + 1) (g3)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc __cbd3 (rp:W16.t Array256.t, buf:W8.t Array128.t) : W16.t Array256.t = {
    var aux: int;
    
    var mask249_s:W32.t;
    var mask6DB_s:W32.t;
    var mask07_s:W32.t;
    var mask70_s:W32.t;
    var mask3_s:W16.t;
    var mask249:W256.t;
    var mask6DB:W256.t;
    var mask07:W256.t;
    var mask70:W256.t;
    var mask3:W256.t;
    var shufbidx:W256.t;
    var i:int;
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var f3:W256.t;
    
    mask249_s <- (W32.of_int 2396745);
    mask6DB_s <- (W32.of_int 7190235);
    mask07_s <- (W32.of_int 7);
    mask70_s <- (W32.of_int (7 `<<` 16));
    mask3_s <- (W16.of_int 3);
    mask249 <- VPBROADCAST_8u32 mask249_s;
    mask6DB <- VPBROADCAST_8u32 mask6DB_s;
    mask07 <- VPBROADCAST_8u32 mask07_s;
    mask70 <- VPBROADCAST_8u32 mask70_s;
    mask3 <- VPBROADCAST_16u16 mask3_s;
    shufbidx <-
    (get256 (WArray32.init8 (fun i_0 => (cbd_jshufbidx).[i_0])) 0);
    aux <- (256 %/ 32);
    i <- 0;
    while (i < aux) {
      f0 <-
      (get256_direct (WArray128.init8 (fun i_0 => (buf).[i_0])) (24 * i));
      f0 <- VPERMQ f0 (W8.of_int 148);
      f0 <- VPSHUFB_256 f0 shufbidx;
      f1 <- VPSRL_8u32 f0 (W8.of_int 1);
      f2 <- VPSRL_8u32 f0 (W8.of_int 2);
      f0 <- VPAND_256 mask249 f0;
      f1 <- VPAND_256 mask249 f1;
      f2 <- VPAND_256 mask249 f2;
      f0 <- VPADD_8u32 f0 f1;
      f0 <- VPADD_8u32 f0 f2;
      f1 <- VPSRL_8u32 f0 (W8.of_int 3);
      f0 <- VPADD_8u32 f0 mask6DB;
      f0 <- VPSUB_8u32 f0 f1;
      f1 <- VPSLL_8u32 f0 (W8.of_int 10);
      f2 <- VPSRL_8u32 f0 (W8.of_int 12);
      f3 <- VPSRL_8u32 f0 (W8.of_int 2);
      f0 <- VPAND_256 f0 mask07;
      f1 <- VPAND_256 f1 mask70;
      f2 <- VPAND_256 f2 mask07;
      f3 <- VPAND_256 f3 mask70;
      f0 <- VPADD_16u16 f0 f1;
      f1 <- VPADD_16u16 f2 f3;
      f0 <- VPSUB_16u16 f0 mask3;
      f1 <- VPSUB_16u16 f1 mask3;
      f2 <- VPUNPCKL_8u32 f0 f1;
      f3 <- VPUNPCKH_8u32 f0 f1;
      f0 <- VPERM2I128 f2 f3 (W8.of_int 32);
      f1 <- VPERM2I128 f2 f3 (W8.of_int 49);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) (2 * i) (f0)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((2 * i) + 1) (f1)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc __cbd2 (rp:W16.t Array256.t, buf:W8.t Array128.t) : W16.t Array256.t = {
    var aux: int;
    
    var mask55_s:W32.t;
    var mask33_s:W32.t;
    var mask03_s:W32.t;
    var mask0F_s:W32.t;
    var mask55:W256.t;
    var mask33:W256.t;
    var mask03:W256.t;
    var mask0F:W256.t;
    var i:int;
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var f3:W256.t;
    var t:W128.t;
    
    mask55_s <- (W32.of_int 1431655765);
    mask33_s <- (W32.of_int 858993459);
    mask03_s <- (W32.of_int 50529027);
    mask0F_s <- (W32.of_int 252645135);
    mask55 <- VPBROADCAST_8u32 mask55_s;
    mask33 <- VPBROADCAST_8u32 mask33_s;
    mask03 <- VPBROADCAST_8u32 mask03_s;
    mask0F <- VPBROADCAST_8u32 mask0F_s;
    aux <- (256 %/ 64);
    i <- 0;
    while (i < aux) {
      f0 <- (get256 (WArray128.init8 (fun i_0 => (buf).[i_0])) i);
      f1 <- VPSRL_16u16 f0 (W8.of_int 1);
      f0 <- VPAND_256 mask55 f0;
      f1 <- VPAND_256 mask55 f1;
      f0 <- VPADD_32u8 f0 f1;
      f1 <- VPSRL_16u16 f0 (W8.of_int 2);
      f0 <- VPAND_256 mask33 f0;
      f1 <- VPAND_256 mask33 f1;
      f0 <- VPADD_32u8 f0 mask33;
      f0 <- VPSUB_32u8 f0 f1;
      f1 <- VPSRL_16u16 f0 (W8.of_int 4);
      f0 <- VPAND_256 mask0F f0;
      f1 <- VPAND_256 mask0F f1;
      f0 <- VPSUB_32u8 f0 mask03;
      f1 <- VPSUB_32u8 f1 mask03;
      f2 <- VPUNPCKL_32u8 f0 f1;
      f3 <- VPUNPCKH_32u8 f0 f1;
      t <- (truncateu128 f2);
      f0 <- VPMOVSX_16u8_16u16 t;
      t <- VEXTRACTI128 f2 (W8.of_int 1);
      f1 <- VPMOVSX_16u8_16u16 t;
      t <- (truncateu128 f3);
      f2 <- VPMOVSX_16u8_16u16 t;
      t <- VEXTRACTI128 f3 (W8.of_int 1);
      f3 <- VPMOVSX_16u8_16u16 t;
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) (4 * i) (f0)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((4 * i) + 1) (f2)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((4 * i) + 2) (f1)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256 (WArray512.init16 (fun i_0 => (rp).[i_0])) ((4 * i) + 3) (f3)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc __poly_cbd_eta1 (rp:W16.t Array256.t, buf:W8.t Array128.t) : W16.t Array256.t = {
    
    
    
    if ((2 = 2)) {
      rp <@ __cbd2 (rp, (Array128.init (fun i => buf.[0 + i])));
    } else {
      rp <@ __cbd3 (rp, buf);
    }
    return (rp);
  }
  
  proc __shake256_squeezenblocks4x (state:W256.t Array25.t,
                                    buf0:W8.t Array136.t,
                                    buf1:W8.t Array136.t,
                                    buf2:W8.t Array136.t,
                                    buf3:W8.t Array136.t) : W256.t Array25.t *
                                                            W8.t Array136.t *
                                                            W8.t Array136.t *
                                                            W8.t Array136.t *
                                                            W8.t Array136.t = {
    var aux: int;
    var aux_4: W8.t Array136.t;
    var aux_3: W8.t Array136.t;
    var aux_2: W8.t Array136.t;
    var aux_1: W8.t Array136.t;
    var aux_0: W256.t Array25.t;
    
    var i:int;
    
    aux <- (((((2 * 256) %/ 4) + 136) - 1) %/ 136);
    i <- 0;
    while (i < aux) {
      (aux_0, aux_4, aux_3, aux_2,
      aux_1) <@ __shake256_squeezeblock4x (state,
      (Array136.init (fun i_0 => buf0.[(i * 136) + i_0])),
      (Array136.init (fun i_0 => buf1.[(i * 136) + i_0])),
      (Array136.init (fun i_0 => buf2.[(i * 136) + i_0])),
      (Array136.init (fun i_0 => buf3.[(i * 136) + i_0])));
      state <- aux_0;
      buf0 <- Array136.init
              (fun i_0 => if (i * 136) <= i_0 < (i * 136) + 136
              then aux_4.[i_0-(i * 136)] else buf0.[i_0]);
      buf1 <- Array136.init
              (fun i_0 => if (i * 136) <= i_0 < (i * 136) + 136
              then aux_3.[i_0-(i * 136)] else buf1.[i_0]);
      buf2 <- Array136.init
              (fun i_0 => if (i * 136) <= i_0 < (i * 136) + 136
              then aux_2.[i_0-(i * 136)] else buf2.[i_0]);
      buf3 <- Array136.init
              (fun i_0 => if (i * 136) <= i_0 < (i * 136) + 136
              then aux_1.[i_0-(i * 136)] else buf3.[i_0]);
      i <- i + 1;
    }
    return (state, buf0, buf1, buf2, buf3);
  }
  
  proc _poly_getnoise_eta1_4x (r0:W16.t Array256.t, r1:W16.t Array256.t,
                               r2:W16.t Array256.t, r3:W16.t Array256.t,
                               seed:W8.t Array32.t, nonce:W8.t) : W16.t Array256.t *
                                                                  W16.t Array256.t *
                                                                  W16.t Array256.t *
                                                                  W16.t Array256.t = {
    
    var f:W256.t;
    var buf0:W8.t Array136.t;
    var buf1:W8.t Array136.t;
    var buf2:W8.t Array136.t;
    var buf3:W8.t Array136.t;
    var state:W256.t Array25.t;
    buf0 <- witness;
    buf1 <- witness;
    buf2 <- witness;
    buf3 <- witness;
    state <- witness;
    f <- (get256 (WArray32.init8 (fun i => (seed).[i])) 0);
    buf0 <-
    Array136.init
    (WArray136.get8 (WArray136.set256 (WArray136.init8 (fun i => (buf0).[i])) 0 (f)));
    buf1 <-
    Array136.init
    (WArray136.get8 (WArray136.set256 (WArray136.init8 (fun i => (buf1).[i])) 0 (f)));
    buf2 <-
    Array136.init
    (WArray136.get8 (WArray136.set256 (WArray136.init8 (fun i => (buf2).[i])) 0 (f)));
    buf3 <-
    Array136.init
    (WArray136.get8 (WArray136.set256 (WArray136.init8 (fun i => (buf3).[i])) 0 (f)));
    buf0 <-
    Array136.init
    (WArray136.get8 (WArray136.set8_direct (WArray136.init8 (fun i => (buf0).[i])) 32 (nonce)));
    nonce <- (nonce + (W8.of_int 1));
    buf1 <-
    Array136.init
    (WArray136.get8 (WArray136.set8_direct (WArray136.init8 (fun i => (buf1).[i])) 32 (nonce)));
    nonce <- (nonce + (W8.of_int 1));
    buf2 <-
    Array136.init
    (WArray136.get8 (WArray136.set8_direct (WArray136.init8 (fun i => (buf2).[i])) 32 (nonce)));
    nonce <- (nonce + (W8.of_int 1));
    buf3 <-
    Array136.init
    (WArray136.get8 (WArray136.set8_direct (WArray136.init8 (fun i => (buf3).[i])) 32 (nonce)));
    state <@ _shake256_absorb4x_33 (state,
    (Array33.init (fun i => buf0.[0 + i])),
    (Array33.init (fun i => buf1.[0 + i])),
    (Array33.init (fun i => buf2.[0 + i])),
    (Array33.init (fun i => buf3.[0 + i])));
    (state, buf0, buf1, buf2, buf3) <@ __shake256_squeezenblocks4x (state,
    buf0, buf1, buf2, buf3);
    r0 <@ __poly_cbd_eta1 (r0, (Array128.init (fun i => buf0.[0 + i])));
    r1 <@ __poly_cbd_eta1 (r1, (Array128.init (fun i => buf1.[0 + i])));
    r2 <@ __poly_cbd_eta1 (r2, (Array128.init (fun i => buf2.[0 + i])));
    r3 <@ __poly_cbd_eta1 (r3, (Array128.init (fun i => buf3.[0 + i])));
    return (r0, r1, r2, r3);
  }
  
  proc __invntt___butterfly64x (rl0:W256.t, rl1:W256.t, rl2:W256.t,
                                rl3:W256.t, rh0:W256.t, rh1:W256.t,
                                rh2:W256.t, rh3:W256.t, zl0:W256.t,
                                zl1:W256.t, zh0:W256.t, zh1:W256.t,
                                qx16:W256.t) : W256.t * W256.t * W256.t *
                                               W256.t * W256.t * W256.t *
                                               W256.t * W256.t = {
    
    var t0:W256.t;
    var t1:W256.t;
    var t2:W256.t;
    var t3:W256.t;
    
    t0 <- VPSUB_16u16 rl0 rh0;
    t1 <- VPSUB_16u16 rl1 rh1;
    t2 <- VPSUB_16u16 rl2 rh2;
    rl0 <- VPADD_16u16 rh0 rl0;
    rl1 <- VPADD_16u16 rh1 rl1;
    rh0 <- VPMULL_16u16 zl0 t0;
    rl2 <- VPADD_16u16 rh2 rl2;
    rh1 <- VPMULL_16u16 zl0 t1;
    t3 <- VPSUB_16u16 rl3 rh3;
    rl3 <- VPADD_16u16 rh3 rl3;
    rh2 <- VPMULL_16u16 zl1 t2;
    rh3 <- VPMULL_16u16 zl1 t3;
    t0 <- VPMULH_16u16 zh0 t0;
    t1 <- VPMULH_16u16 zh0 t1;
    t2 <- VPMULH_16u16 zh1 t2;
    t3 <- VPMULH_16u16 zh1 t3;
    rh0 <- VPMULH_16u16 qx16 rh0;
    rh1 <- VPMULH_16u16 qx16 rh1;
    rh2 <- VPMULH_16u16 qx16 rh2;
    rh3 <- VPMULH_16u16 qx16 rh3;
    rh0 <- VPSUB_16u16 t0 rh0;
    rh1 <- VPSUB_16u16 t1 rh1;
    rh2 <- VPSUB_16u16 t2 rh2;
    rh3 <- VPSUB_16u16 t3 rh3;
    return (rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3);
  }
  
  proc _poly_invntt (rp:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var zetasp:W16.t Array400.t;
    var qx16:W256.t;
    var i:int;
    var zeta0:W256.t;
    var zeta1:W256.t;
    var zeta2:W256.t;
    var zeta3:W256.t;
    var r0:W256.t;
    var r1:W256.t;
    var r2:W256.t;
    var r3:W256.t;
    var r4:W256.t;
    var r5:W256.t;
    var r6:W256.t;
    var r7:W256.t;
    var vx16:W256.t;
    var flox16:W256.t;
    var fhix16:W256.t;
    zetasp <- witness;
    zetasp <- jzetas_inv_exp;
    qx16 <- (get256 (WArray32.init16 (fun i_0 => (jqx16).[i_0])) 0);
    i <- 0;
    while (i < 2) {
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (0 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (64 + (392 * i)));
      zeta2 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (32 + (392 * i)));
      zeta3 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (96 + (392 * i)));
      r0 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 0) + (256 * i)));
      r1 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 1) + (256 * i)));
      r2 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 2) + (256 * i)));
      r3 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 3) + (256 * i)));
      r4 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 4) + (256 * i)));
      r5 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 5) + (256 * i)));
      r6 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 6) + (256 * i)));
      r7 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 7) + (256 * i)));
      (r0, r1, r4, r5, r2, r3, r6, r7) <@ __invntt___butterfly64x (r0, r1,
      r4, r5, r2, r3, r6, r7, zeta0, zeta1, zeta2, zeta3, qx16);
      vx16 <- (get256 (WArray32.init16 (fun i_0 => (jvx16).[i_0])) 0);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (128 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (160 + (392 * i)));
      r0 <@ __red16x (r0, qx16, vx16);
      r1 <@ __red16x (r1, qx16, vx16);
      r4 <@ __red16x (r4, qx16, vx16);
      r5 <@ __red16x (r5, qx16, vx16);
      (r0, r1, r2, r3, r4, r5, r6, r7) <@ __invntt___butterfly64x (r0, r1,
      r2, r3, r4, r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      (r0, r1) <@ __shuffle1 (r0, r1);
      (r2, r3) <@ __shuffle1 (r2, r3);
      (r4, r5) <@ __shuffle1 (r4, r5);
      (r6, r7) <@ __shuffle1 (r6, r7);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (192 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (224 + (392 * i)));
      (r0, r2, r4, r6, r1, r3, r5, r7) <@ __invntt___butterfly64x (r0, r2,
      r4, r6, r1, r3, r5, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      r0 <@ __red16x (r0, qx16, vx16);
      (r0, r2) <@ __shuffle2 (r0, r2);
      (r4, r6) <@ __shuffle2 (r4, r6);
      (r1, r3) <@ __shuffle2 (r1, r3);
      (r5, r7) <@ __shuffle2 (r5, r7);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (256 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (288 + (392 * i)));
      (r0, r4, r1, r5, r2, r6, r3, r7) <@ __invntt___butterfly64x (r0, r4,
      r1, r5, r2, r6, r3, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      r0 <@ __red16x (r0, qx16, vx16);
      (r0, r4) <@ __shuffle4 (r0, r4);
      (r1, r5) <@ __shuffle4 (r1, r5);
      (r2, r6) <@ __shuffle4 (r2, r6);
      (r3, r7) <@ __shuffle4 (r3, r7);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (320 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (352 + (392 * i)));
      (r0, r1, r2, r3, r4, r5, r6, r7) <@ __invntt___butterfly64x (r0, r1,
      r2, r3, r4, r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      r0 <@ __red16x (r0, qx16, vx16);
      (r0, r1) <@ __shuffle8 (r0, r1);
      (r2, r3) <@ __shuffle8 (r2, r3);
      (r4, r5) <@ __shuffle8 (r4, r5);
      (r6, r7) <@ __shuffle8 (r6, r7);
      zeta0 <-
      VPBROADCAST_8u32 (get32_direct
                       (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
                       (384 + (392 * i)));
      zeta1 <-
      VPBROADCAST_8u32 (get32_direct
                       (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
                       (388 + (392 * i)));
      (r0, r2, r4, r6, r1, r3, r5, r7) <@ __invntt___butterfly64x (r0, r2,
      r4, r6, r1, r3, r5, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      r0 <@ __red16x (r0, qx16, vx16);
      if ((i = 0)) {
        rp <-
        Array256.init
        (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 0) + (256 * i)) (r0)));
        rp <-
        Array256.init
        (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 1) + (256 * i)) (r2)));
        rp <-
        Array256.init
        (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 2) + (256 * i)) (r4)));
        rp <-
        Array256.init
        (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 3) + (256 * i)) (r6)));
      } else {
        
      }
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 4) + (256 * i)) (r1)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 5) + (256 * i)) (r3)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 6) + (256 * i)) (r5)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 7) + (256 * i)) (r7)));
      i <- i + 1;
    }
    zeta0 <-
    VPBROADCAST_8u32 (get32_direct
                     (WArray800.init16 (fun i_0 => (zetasp).[i_0])) 784);
    zeta1 <-
    VPBROADCAST_8u32 (get32_direct
                     (WArray800.init16 (fun i_0 => (zetasp).[i_0])) 788);
    i <- 0;
    while (i < 2) {
      if ((i = 0)) {
        r7 <- r6;
        r6 <- r4;
        r5 <- r2;
        r4 <- r0;
      } else {
        r4 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 8) + (128 * i)));
        r5 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 9) + (128 * i)));
        r6 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 10) + (128 * i)));
        r7 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 11) + (128 * i)));
      }
      r0 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 0) + (128 * i)));
      r1 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 1) + (128 * i)));
      r2 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 2) + (128 * i)));
      r3 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 3) + (128 * i)));
      (r0, r1, r2, r3, r4, r5, r6, r7) <@ __invntt___butterfly64x (r0, r1,
      r2, r3, r4, r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      flox16 <- (get256 (WArray32.init16 (fun i_0 => (jflox16).[i_0])) 0);
      fhix16 <- (get256 (WArray32.init16 (fun i_0 => (jfhix16).[i_0])) 0);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 8) + (128 * i)) (r4)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 9) + (128 * i)) (r5)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 10) + (128 * i)) (r6)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 11) + (128 * i)) (r7)));
      r0 <@ __fqmulprecomp16x (r0, flox16, fhix16, qx16);
      r1 <@ __fqmulprecomp16x (r1, flox16, fhix16, qx16);
      r2 <@ __fqmulprecomp16x (r2, flox16, fhix16, qx16);
      r3 <@ __fqmulprecomp16x (r3, flox16, fhix16, qx16);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 0) + (128 * i)) (r0)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 1) + (128 * i)) (r1)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 2) + (128 * i)) (r2)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 3) + (128 * i)) (r3)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc __butterfly64x (rl0:W256.t, rl1:W256.t, rl2:W256.t, rl3:W256.t,
                       rh0:W256.t, rh1:W256.t, rh2:W256.t, rh3:W256.t,
                       zl0:W256.t, zl1:W256.t, zh0:W256.t, zh1:W256.t,
                       qx16:W256.t) : W256.t * W256.t * W256.t * W256.t *
                                      W256.t * W256.t * W256.t * W256.t = {
    
    var t0:W256.t;
    var t1:W256.t;
    var t2:W256.t;
    var t3:W256.t;
    var t4:W256.t;
    var t5:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    
    t0 <- VPMULL_16u16 zl0 rh0;
    t1 <- VPMULH_16u16 zh0 rh0;
    t2 <- VPMULL_16u16 zl0 rh1;
    t3 <- VPMULH_16u16 zh0 rh1;
    t4 <- VPMULL_16u16 zl1 rh2;
    t5 <- VPMULH_16u16 zh1 rh2;
    t6 <- VPMULL_16u16 zl1 rh3;
    t7 <- VPMULH_16u16 zh1 rh3;
    t0 <- VPMULH_16u16 t0 qx16;
    t2 <- VPMULH_16u16 t2 qx16;
    t4 <- VPMULH_16u16 t4 qx16;
    t6 <- VPMULH_16u16 t6 qx16;
    rh1 <- VPSUB_16u16 rl1 t3;
    rl1 <- VPADD_16u16 t3 rl1;
    rh0 <- VPSUB_16u16 rl0 t1;
    rl0 <- VPADD_16u16 t1 rl0;
    rh3 <- VPSUB_16u16 rl3 t7;
    rl3 <- VPADD_16u16 t7 rl3;
    rh2 <- VPSUB_16u16 rl2 t5;
    rl2 <- VPADD_16u16 t5 rl2;
    rh0 <- VPADD_16u16 t0 rh0;
    rl0 <- VPSUB_16u16 rl0 t0;
    rh1 <- VPADD_16u16 t2 rh1;
    rl1 <- VPSUB_16u16 rl1 t2;
    rh2 <- VPADD_16u16 t4 rh2;
    rl2 <- VPSUB_16u16 rl2 t4;
    rh3 <- VPADD_16u16 t6 rh3;
    rl3 <- VPSUB_16u16 rl3 t6;
    return (rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3);
  }
  
  proc _poly_ntt (rp:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var zetasp:W16.t Array400.t;
    var qx16:W256.t;
    var zeta0:W256.t;
    var zeta1:W256.t;
    var r0:W256.t;
    var r1:W256.t;
    var r2:W256.t;
    var r3:W256.t;
    var r4:W256.t;
    var r5:W256.t;
    var r6:W256.t;
    var r7:W256.t;
    var i:int;
    var zeta2:W256.t;
    var zeta3:W256.t;
    var vx16:W256.t;
    zetasp <- witness;
    zetasp <- jzetas_exp;
    qx16 <- (get256 (WArray32.init16 (fun i_0 => (jqx16).[i_0])) 0);
    zeta0 <-
    VPBROADCAST_8u32 (get32 (WArray800.init16 (fun i_0 => (zetasp).[i_0])) 0);
    zeta1 <-
    VPBROADCAST_8u32 (get32 (WArray800.init16 (fun i_0 => (zetasp).[i_0])) 1);
    r0 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 0));
    r1 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 1));
    r2 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 2));
    r3 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 3));
    r4 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 8));
    r5 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 9));
    r6 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 10));
    r7 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 11));
    (r0, r1, r2, r3, r4, r5, r6, r7) <@ __butterfly64x (r0, r1, r2, r3, r4,
    r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 0) (r0)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 1) (r1)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 2) (r2)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 3) (r3)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 8) (r4)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 9) (r5)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 10) (r6)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 11) (r7)));
    r0 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 4));
    r1 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 5));
    r2 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 6));
    r3 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 7));
    r4 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 12));
    r5 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 13));
    r6 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 14));
    r7 <-
    (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 15));
    (r0, r1, r2, r3, r4, r5, r6, r7) <@ __butterfly64x (r0, r1, r2, r3, r4,
    r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 12) (r4)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 13) (r5)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 14) (r6)));
    rp <-
    Array256.init
    (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * 15) (r7)));
    i <- 0;
    while (i < 2) {
      zeta0 <-
      VPBROADCAST_8u32 (get32_direct
                       (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
                       (8 + (392 * i)));
      zeta1 <-
      VPBROADCAST_8u32 (get32_direct
                       (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
                       (12 + (392 * i)));
      if ((i = 0)) {
        r4 <- r0;
        r5 <- r1;
        r6 <- r2;
        r7 <- r3;
      } else {
        r4 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 4) + (256 * i)));
        r5 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 5) + (256 * i)));
        r6 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 6) + (256 * i)));
        r7 <-
        (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
        ((32 * 7) + (256 * i)));
      }
      r0 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 0) + (256 * i)));
      r1 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 1) + (256 * i)));
      r2 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 2) + (256 * i)));
      r3 <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0]))
      ((32 * 3) + (256 * i)));
      (r0, r1, r2, r3, r4, r5, r6, r7) <@ __butterfly64x (r0, r1, r2, r3, r4,
      r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (16 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (48 + (392 * i)));
      (r0, r4) <@ __shuffle8 (r0, r4);
      (r1, r5) <@ __shuffle8 (r1, r5);
      (r2, r6) <@ __shuffle8 (r2, r6);
      (r3, r7) <@ __shuffle8 (r3, r7);
      (r0, r4, r1, r5, r2, r6, r3, r7) <@ __butterfly64x (r0, r4, r1, r5, r2,
      r6, r3, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (80 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (112 + (392 * i)));
      (r0, r2) <@ __shuffle4 (r0, r2);
      (r4, r6) <@ __shuffle4 (r4, r6);
      (r1, r3) <@ __shuffle4 (r1, r3);
      (r5, r7) <@ __shuffle4 (r5, r7);
      (r0, r2, r4, r6, r1, r3, r5, r7) <@ __butterfly64x (r0, r2, r4, r6, r1,
      r3, r5, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (144 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (176 + (392 * i)));
      (r0, r1) <@ __shuffle2 (r0, r1);
      (r2, r3) <@ __shuffle2 (r2, r3);
      (r4, r5) <@ __shuffle2 (r4, r5);
      (r6, r7) <@ __shuffle2 (r6, r7);
      (r0, r1, r2, r3, r4, r5, r6, r7) <@ __butterfly64x (r0, r1, r2, r3, r4,
      r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (208 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (240 + (392 * i)));
      (r0, r4) <@ __shuffle1 (r0, r4);
      (r1, r5) <@ __shuffle1 (r1, r5);
      (r2, r6) <@ __shuffle1 (r2, r6);
      (r3, r7) <@ __shuffle1 (r3, r7);
      (r0, r4, r1, r5, r2, r6, r3, r7) <@ __butterfly64x (r0, r4, r1, r5, r2,
      r6, r3, r7, zeta0, zeta0, zeta1, zeta1, qx16);
      zeta0 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (272 + (392 * i)));
      zeta2 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (304 + (392 * i)));
      zeta1 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (336 + (392 * i)));
      zeta3 <-
      (get256_direct (WArray800.init16 (fun i_0 => (zetasp).[i_0]))
      (368 + (392 * i)));
      (r0, r4, r2, r6, r1, r5, r3, r7) <@ __butterfly64x (r0, r4, r2, r6, r1,
      r5, r3, r7, zeta0, zeta1, zeta2, zeta3, qx16);
      vx16 <- (get256 (WArray32.init16 (fun i_0 => (jvx16).[i_0])) 0);
      r0 <@ __red16x (r0, qx16, vx16);
      r4 <@ __red16x (r4, qx16, vx16);
      r2 <@ __red16x (r2, qx16, vx16);
      r6 <@ __red16x (r6, qx16, vx16);
      r1 <@ __red16x (r1, qx16, vx16);
      r5 <@ __red16x (r5, qx16, vx16);
      r3 <@ __red16x (r3, qx16, vx16);
      r7 <@ __red16x (r7, qx16, vx16);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 0) + (256 * i)) (r0)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 1) + (256 * i)) (r4)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 2) + (256 * i)) (r1)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 3) + (256 * i)) (r5)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 4) + (256 * i)) (r2)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 5) + (256 * i)) (r6)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 6) + (256 * i)) (r3)));
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) ((32 * 7) + (256 * i)) (r7)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc __poly_reduce (rp:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var qx16:W256.t;
    var vx16:W256.t;
    var i:int;
    var r:W256.t;
    
    qx16 <- (get256 (WArray32.init16 (fun i_0 => (jqx16).[i_0])) 0);
    vx16 <- (get256 (WArray32.init16 (fun i_0 => (jvx16).[i_0])) 0);
    i <- 0;
    while (i < 16) {
      r <-
      (get256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * i));
      r <@ __red16x (r, qx16, vx16);
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * i) (r)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_sub (rp:W16.t Array256.t, ap:W16.t Array256.t,
                  bp:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var i:int;
    var a:W256.t;
    var b:W256.t;
    var r:W256.t;
    
    i <- 0;
    while (i < 16) {
      a <-
      (get256_direct (WArray512.init16 (fun i_0 => (ap).[i_0])) (32 * i));
      b <-
      (get256_direct (WArray512.init16 (fun i_0 => (bp).[i_0])) (32 * i));
      r <- VPSUB_16u16 a b;
      rp <-
      Array256.init
      (WArray512.get16 (WArray512.set256_direct (WArray512.init16 (fun i_0 => (rp).[i_0])) (32 * i) (r)));
      i <- i + 1;
    }
    return (rp);
  }
  
  proc _poly_tobytes (rp:W64.t, a:W16.t Array256.t) : W16.t Array256.t = {
    var aux: int;
    
    var jqx16_p:W16.t Array16.t;
    var qx16:W256.t;
    var i:int;
    var t0:W256.t;
    var t1:W256.t;
    var t2:W256.t;
    var t3:W256.t;
    var t4:W256.t;
    var t5:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    var tt:W256.t;
    var ttt:W256.t;
    jqx16_p <- witness;
    jqx16_p <- jqx16;
    qx16 <- (get256 (WArray32.init16 (fun i_0 => (jqx16_p).[i_0])) 0);
    a <@ _poly_csubq (a);
    i <- 0;
    while (i < 2) {
      t0 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) (8 * i));
      t1 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((8 * i) + 1));
      t2 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((8 * i) + 2));
      t3 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((8 * i) + 3));
      t4 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((8 * i) + 4));
      t5 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((8 * i) + 5));
      t6 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((8 * i) + 6));
      t7 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((8 * i) + 7));
      tt <- VPSLL_16u16 t1 (W8.of_int 12);
      tt <- (tt `|` t0);
      t0 <- VPSRL_16u16 t1 (W8.of_int 4);
      t1 <- VPSLL_16u16 t2 (W8.of_int 8);
      t0 <- (t0 `|` t1);
      t1 <- VPSRL_16u16 t2 (W8.of_int 8);
      t2 <- VPSLL_16u16 t3 (W8.of_int 4);
      t1 <- (t1 `|` t2);
      t2 <- VPSLL_16u16 t5 (W8.of_int 12);
      t2 <- (t2 `|` t4);
      t3 <- VPSRL_16u16 t5 (W8.of_int 4);
      t4 <- VPSLL_16u16 t6 (W8.of_int 8);
      t3 <- (t3 `|` t4);
      t4 <- VPSRL_16u16 t6 (W8.of_int 8);
      t5 <- VPSLL_16u16 t7 (W8.of_int 4);
      t4 <- (t4 `|` t5);
      (ttt, t0) <@ __shuffle1 (tt, t0);
      (tt, t2) <@ __shuffle1 (t1, t2);
      (t1, t4) <@ __shuffle1 (t3, t4);
      (t3, tt) <@ __shuffle2 (ttt, tt);
      (ttt, t0) <@ __shuffle2 (t1, t0);
      (t1, t4) <@ __shuffle2 (t2, t4);
      (t2, ttt) <@ __shuffle4 (t3, ttt);
      (t3, tt) <@ __shuffle4 (t1, tt);
      (t1, t4) <@ __shuffle4 (t0, t4);
      (t0, t3) <@ __shuffle8 (t2, t3);
      (t2, ttt) <@ __shuffle8 (t1, ttt);
      (t1, t4) <@ __shuffle8 (tt, t4);
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int (192 * i)))) (t0);
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int ((192 * i) + 32)))) (t2);
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int ((192 * i) + 64)))) (t1);
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int ((192 * i) + 96)))) (t3);
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int ((192 * i) + 128)))) (ttt);
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int ((192 * i) + 160)))) (t4);
      i <- i + 1;
    }
    return (a);
  }
  
  proc _poly_tomsg_1 (rp:W8.t Array32.t, a:W16.t Array256.t) : W8.t Array32.t *
                                                               W16.t Array256.t = {
    var aux: int;
    
    var px16:W16.t Array16.t;
    var hq:W256.t;
    var hhq:W256.t;
    var i:int;
    var f0:W256.t;
    var f1:W256.t;
    var g0:W256.t;
    var g1:W256.t;
    var c:W32.t;
    px16 <- witness;
    a <@ _poly_csubq (a);
    px16 <- hqx16_m1;
    hq <- (get256 (WArray32.init16 (fun i_0 => (px16).[i_0])) 0);
    px16 <- hhqx16;
    hhq <- (get256 (WArray32.init16 (fun i_0 => (px16).[i_0])) 0);
    aux <- (256 %/ 32);
    i <- 0;
    while (i < aux) {
      f0 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) (2 * i));
      f1 <- (get256 (WArray512.init16 (fun i_0 => (a).[i_0])) ((2 * i) + 1));
      f0 <- VPSUB_16u16 hq f0;
      f1 <- VPSUB_16u16 hq f1;
      g0 <- VPSRA_16u16 f0 (W8.of_int 15);
      g1 <- VPSRA_16u16 f1 (W8.of_int 15);
      f0 <- VPXOR_256 f0 g0;
      f1 <- VPXOR_256 f1 g1;
      f0 <- VPSUB_16u16 f0 hhq;
      f1 <- VPSUB_16u16 f1 hhq;
      f0 <- VPACKSS_16u16 f0 f1;
      f0 <- VPERMQ f0 (W8.of_int 216);
      c <- VPMOVMSKB_u256u32 f0;
      rp <-
      Array32.init
      (WArray32.get8 (WArray32.set32 (WArray32.init8 (fun i_0 => (rp).[i_0])) i (c)));
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
  
  proc __polyvec_decompress (rp:W64.t) : W16.t Array768.t = {
    var aux: int;
    
    var r:W16.t Array768.t;
    var q:W256.t;
    var shufbidx:W256.t;
    var sllvdidx:W256.t;
    var mask:W256.t;
    var i:int;
    var k:int;
    var f:W256.t;
    r <- witness;
    q <- VPBROADCAST_8u32 pvd_q_s;
    shufbidx <-
    (get256 (WArray32.init8 (fun i_0 => (pvd_shufbdidx_s).[i_0])) 0);
    sllvdidx <- VPBROADCAST_4u64 pvd_sllvdidx_s;
    mask <- VPBROADCAST_8u32 pvd_mask_s;
    k <- 0;
    while (k < 3) {
      aux <- (256 %/ 16);
      i <- 0;
      while (i < aux) {
        f <-
        (loadW256 Glob.mem (W64.to_uint (rp + (W64.of_int ((320 * k) + (20 * i))))));
        f <- VPERMQ f (W8.of_int 148);
        f <- VPSHUFB_256 f shufbidx;
        f <- VPSLLV_8u32 f sllvdidx;
        f <- VPSRL_16u16 f (W8.of_int 1);
        f <- VPAND_256 f mask;
        f <- VPMULHRS_16u16 f q;
        r <-
        Array768.init
        (WArray1536.get16 (WArray1536.set256 (WArray1536.init16 (fun i_0 => (r).[i_0])) ((16 * k) + i) (f)));
        i <- i + 1;
      }
      k <- k + 1;
    }
    return (r);
  }
  
  proc __polyvec_compress (rp:W64.t, a:W16.t Array768.t) : unit = {
    var aux: int;
    
    var x16p:W16.t Array16.t;
    var v:W256.t;
    var v8:W256.t;
    var off:W256.t;
    var shift1:W256.t;
    var mask:W256.t;
    var shift2:W256.t;
    var sllvdidx:W256.t;
    var shufbidx:W256.t;
    var i:int;
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var t0:W128.t;
    var t1:W128.t;
    x16p <- witness;
    a <@ __polyvec_csubq (a);
    x16p <- jvx16;
    v <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    v8 <- VPSLL_16u16 v (W8.of_int 3);
    off <- VPBROADCAST_16u16 pvc_off_s;
    shift1 <- VPBROADCAST_16u16 pvc_shift1_s;
    mask <- VPBROADCAST_16u16 pvc_mask_s;
    shift2 <- VPBROADCAST_4u64 pvc_shift2_s;
    sllvdidx <- VPBROADCAST_4u64 pvc_sllvdidx_s;
    shufbidx <-
    (get256 (WArray32.init8 (fun i_0 => (pvc_shufbidx_s).[i_0])) 0);
    aux <- ((3 * 256) %/ 16);
    i <- 0;
    while (i < aux) {
      f0 <- (get256 (WArray1536.init16 (fun i_0 => (a).[i_0])) i);
      f1 <- VPMULL_16u16 f0 v8;
      f2 <- VPADD_16u16 f0 off;
      f0 <- VPSLL_16u16 f0 (W8.of_int 3);
      f0 <- VPMULH_16u16 f0 v;
      f2 <- VPSUB_16u16 f1 f2;
      f1 <- VPANDN_256 f1 f2;
      f1 <- VPSRL_16u16 f1 (W8.of_int 15);
      f0 <- VPSUB_16u16 f0 f1;
      f0 <- VPMULHRS_16u16 f0 shift1;
      f0 <- VPAND_256 f0 mask;
      f0 <- VPMADDWD_256 f0 shift2;
      f0 <- VPSLLV_8u32 f0 sllvdidx;
      f0 <- VPSRL_4u64 f0 (W8.of_int 12);
      f0 <- VPSHUFB_256 f0 shufbidx;
      t0 <- (truncateu128 f0);
      t1 <- VEXTRACTI128 f0 (W8.of_int 1);
      t0 <- VPBLEND_8u16 t0 t1 (W8.of_int 224);
      Glob.mem <-
      storeW128 Glob.mem (W64.to_uint (rp + (W64.of_int (20 * i)))) (t0);
      Glob.mem <-
      storeW32 Glob.mem (W64.to_uint (rp + (W64.of_int ((20 * i) + 16)))) (VPEXTR_32 t1
      (W8.of_int 0));
      i <- i + 1;
    }
    return ();
  }
  
  proc __polyvec_compress_1 (rp:W8.t Array960.t, a:W16.t Array768.t) : 
  W8.t Array960.t = {
    var aux: int;
    
    var x16p:W16.t Array16.t;
    var v:W256.t;
    var v8:W256.t;
    var off:W256.t;
    var shift1:W256.t;
    var mask:W256.t;
    var shift2:W256.t;
    var sllvdidx:W256.t;
    var shufbidx:W256.t;
    var i:int;
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var t0:W128.t;
    var t1:W128.t;
    x16p <- witness;
    a <@ __polyvec_csubq (a);
    x16p <- jvx16;
    v <- (get256 (WArray32.init16 (fun i_0 => (x16p).[i_0])) 0);
    v8 <- VPSLL_16u16 v (W8.of_int 3);
    off <- VPBROADCAST_16u16 pvc_off_s;
    shift1 <- VPBROADCAST_16u16 pvc_shift1_s;
    mask <- VPBROADCAST_16u16 pvc_mask_s;
    shift2 <- VPBROADCAST_4u64 pvc_shift2_s;
    sllvdidx <- VPBROADCAST_4u64 pvc_sllvdidx_s;
    shufbidx <-
    (get256 (WArray32.init8 (fun i_0 => (pvc_shufbidx_s).[i_0])) 0);
    aux <- ((3 * 256) %/ 16);
    i <- 0;
    while (i < aux) {
      f0 <- (get256 (WArray1536.init16 (fun i_0 => (a).[i_0])) i);
      f1 <- VPMULL_16u16 f0 v8;
      f2 <- VPADD_16u16 f0 off;
      f0 <- VPSLL_16u16 f0 (W8.of_int 3);
      f0 <- VPMULH_16u16 f0 v;
      f2 <- VPSUB_16u16 f1 f2;
      f1 <- VPANDN_256 f1 f2;
      f1 <- VPSRL_16u16 f1 (W8.of_int 15);
      f0 <- VPSUB_16u16 f0 f1;
      f0 <- VPMULHRS_16u16 f0 shift1;
      f0 <- VPAND_256 f0 mask;
      f0 <- VPMADDWD_256 f0 shift2;
      f0 <- VPSLLV_8u32 f0 sllvdidx;
      f0 <- VPSRL_4u64 f0 (W8.of_int 12);
      f0 <- VPSHUFB_256 f0 shufbidx;
      t0 <- (truncateu128 f0);
      t1 <- VEXTRACTI128 f0 (W8.of_int 1);
      t0 <- VPBLEND_8u16 t0 t1 (W8.of_int 224);
      rp <-
      Array960.init
      (WArray960.get8 (WArray960.set128_direct (WArray960.init8 (fun i_0 => (rp).[i_0])) (20 * i) (t0)));
      rp <-
      Array960.init
      (WArray960.get8 (WArray960.set32_direct (WArray960.init8 (fun i_0 => (rp).[i_0])) ((20 * i) + 16) (VPEXTR_32 t1
      (W8.of_int 0))));
      i <- i + 1;
    }
    return (rp);
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
  
  proc __polyvec_pointwise_acc (r:W16.t Array256.t, a:W16.t Array768.t,
                                b:W16.t Array768.t) : W16.t Array256.t = {
    
    var t:W16.t Array256.t;
    t <- witness;
    r <@ _poly_basemul (r, (Array256.init (fun i => a.[0 + i])),
    (Array256.init (fun i => b.[0 + i])));
    t <@ _poly_basemul (t, (Array256.init (fun i => a.[256 + i])),
    (Array256.init (fun i => b.[256 + i])));
    r <@ _poly_add2 (r, t);
    t <@ _poly_basemul (t, (Array256.init (fun i => a.[(2 * 256) + i])),
    (Array256.init (fun i => b.[(2 * 256) + i])));
    r <@ _poly_add2 (r, t);
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
  
  proc keccakf1600_4x_theta_sum (a:W256.t Array25.t) : W256.t Array5.t = {
    var aux: int;
    
    var c:W256.t Array5.t;
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
  
  proc keccakf1600_4x_rol (a:W256.t Array5.t, x:int, r:int, r8:W256.t,
                           r56:W256.t) : W256.t Array5.t = {
    
    var t:W256.t;
    
    if ((r = 8)) {
      a.[x] <- VPSHUFB_256 a.[x] r8;
    } else {
      if ((r = 56)) {
        a.[x] <- VPSHUFB_256 a.[x] r56;
      } else {
        t <- VPSLL_4u64 a.[x] (W8.of_int r);
        a.[x] <- VPSRL_4u64 a.[x] (W8.of_int (64 - r));
        a.[x] <- (a.[x] `|` t);
      }
    }
    return (a);
  }
  
  proc keccakf1600_4x_theta_rol (c:W256.t Array5.t, r8:W256.t, r56:W256.t) : 
  W256.t Array5.t = {
    var aux: int;
    
    var d:W256.t Array5.t;
    var x:int;
    d <- witness;
    x <- 0;
    while (x < 5) {
      d.[x] <- c.[((x + 1) %% 5)];
      d <@ keccakf1600_4x_rol (d, x, 1, r8, r56);
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- x + 1;
    }
    return (d);
  }
  
  proc keccakf1600_4x_rol_sum (a:W256.t Array25.t, d:W256.t Array5.t, y:int,
                               r8:W256.t, r56:W256.t) : W256.t Array5.t = {
    var aux: int;
    
    var b:W256.t Array5.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    b <- witness;
    x <- 0;
    while (x < 5) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      r <@ keccakf1600_rhotates (x_, y_);
      b.[x] <- a.[(x_ + (y_ * 5))];
      b.[x] <- (b.[x] `^` d.[x_]);
      if ((r <> 0)) {
        b <@ keccakf1600_4x_rol (b, x, r, r8, r56);
      } else {
        
      }
      x <- x + 1;
    }
    return (b);
  }
  
  proc keccakf1600_4x_set_row (e:W256.t Array25.t, b:W256.t Array5.t, y:int,
                               rc:W256.t) : W256.t Array25.t = {
    var aux: int;
    
    var x:int;
    var x1:int;
    var x2:int;
    var t:W256.t;
    
    x <- 0;
    while (x < 5) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <- VPANDN_256 b.[x1] b.[x2];
      t <- (t `^` b.[x]);
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` rc);
      } else {
        
      }
      e.[(x + (y * 5))] <- t;
      x <- x + 1;
    }
    return (e);
  }
  
  proc keccakf1600_4x_round (e:W256.t Array25.t, a:W256.t Array25.t,
                             rc:W256.t, r8:W256.t, r56:W256.t) : W256.t Array25.t = {
    var aux: int;
    
    var c:W256.t Array5.t;
    var d:W256.t Array5.t;
    var y:int;
    var b:W256.t Array5.t;
    b <- witness;
    c <- witness;
    d <- witness;
    c <@ keccakf1600_4x_theta_sum (a);
    d <@ keccakf1600_4x_theta_rol (c, r8, r56);
    y <- 0;
    while (y < 5) {
      b <@ keccakf1600_4x_rol_sum (a, d, y, r8, r56);
      e <@ keccakf1600_4x_set_row (e, b, y, rc);
      y <- y + 1;
    }
    return (e);
  }
  
  proc __keccakf1600_4x (a:W256.t Array25.t) : W256.t Array25.t = {
    
    var rC:W256.t Array24.t;
    var s_e:W256.t Array25.t;
    var e:W256.t Array25.t;
    var r8:W256.t;
    var r56:W256.t;
    var c:W64.t;
    var rc:W256.t;
    var a_s:W256.t Array25.t;
    rC <- witness;
    a_s <- witness;
    e <- witness;
    s_e <- witness;
    rC <- KECCAK1600_RC_AVX2;
    e <- s_e;
    r8 <- ROL8;
    r56 <- ROL56;
    c <- (W64.of_int 0);
    
    while ((c \ult (W64.of_int (24 * 32)))) {
      rc <-
      (get256_direct (WArray768.init256 (fun i => (rC).[i])) (W64.to_uint c));
      e <@ keccakf1600_4x_round (e, a, rc, r8, r56);
      a_s <- a;
      s_e <- e;
      a <- a_s;
      e <- s_e;
      rc <-
      (get256_direct (WArray768.init256 (fun i => (rC).[i]))
      ((W64.to_uint c) + 32));
      a <@ keccakf1600_4x_round (a, e, rc, r8, r56);
      a_s <- a;
      s_e <- e;
      a <- a_s;
      e <- s_e;
      c <- (c + (W64.of_int 64));
    }
    return (a);
  }
  
  proc _keccakf1600_4x_ (a:W256.t Array25.t) : W256.t Array25.t = {
    
    
    
    a <@ __keccakf1600_4x (a);
    return (a);
  }
  
  proc _keccakf1600_4x (a:W256.t Array25.t) : W256.t Array25.t = {
    
    
    
    a <- a;
    a <@ _keccakf1600_4x_ (a);
    a <- a;
    return (a);
  }
  
  proc _keccakf1600_avx2 (state:W256.t Array7.t) : W256.t Array7.t = {
    
    var iotas_p:W256.t Array24.t;
    var iotas_o:W64.t;
    var rhotates_left_p:W256.t Array6.t;
    var rhotates_right_p:W256.t Array6.t;
    var r:W64.t;
    var zf:bool;
    var c00:W256.t;
    var c14:W256.t;
    var t:W256.t Array9.t;
    var d14:W256.t;
    var d00:W256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    iotas_p <- witness;
    rhotates_left_p <- witness;
    rhotates_right_p <- witness;
    t <- witness;
    iotas_p <- KECCAK_IOTAS;
    iotas_o <- (W64.of_int 0);
    rhotates_left_p <- KECCAK_RHOTATES_LEFT;
    rhotates_right_p <- KECCAK_RHOTATES_RIGHT;
    r <- (W64.of_int 24);
    c00 <- VPSHUFD_256 state.[2]
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
    c14 <- (state.[5] `^` state.[3]);
    t.[2] <- (state.[4] `^` state.[6]);
    c14 <- (c14 `^` state.[1]);
    c14 <- (c14 `^` t.[2]);
    t.[4] <- VPERMQ c14
    (W8.of_int (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
    c00 <- (c00 `^` state.[2]);
    t.[0] <- VPERMQ c00
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
    t.[1] <- (c14 \vshr64u256 (W8.of_int 63));
    t.[2] <- (c14 \vadd64u256 c14);
    t.[1] <- (t.[1] `|` t.[2]);
    d14 <- VPERMQ t.[1]
    (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    d00 <- (t.[1] `^` t.[4]);
    d00 <- VPERMQ d00
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    c00 <- (c00 `^` state.[0]);
    c00 <- (c00 `^` t.[0]);
    t.[0] <- (c00 \vshr64u256 (W8.of_int 63));
    t.[1] <- (c00 \vadd64u256 c00);
    t.[1] <- (t.[1] `|` t.[0]);
    state.[2] <- (state.[2] `^` d00);
    state.[0] <- (state.[0] `^` d00);
    d14 <- VPBLEND_8u32 d14 t.[1]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t.[4] <- VPBLEND_8u32 t.[4] c00
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    d14 <- (d14 `^` t.[4]);
    t.[3] <- VPSLLV_4u64 state.[2] rhotates_left_p.[0];
    state.[2] <- VPSRLV_4u64 state.[2] rhotates_right_p.[0];
    state.[2] <- (state.[2] `|` t.[3]);
    state.[3] <- (state.[3] `^` d14);
    t.[4] <- VPSLLV_4u64 state.[3] rhotates_left_p.[2];
    state.[3] <- VPSRLV_4u64 state.[3] rhotates_right_p.[2];
    state.[3] <- (state.[3] `|` t.[4]);
    state.[4] <- (state.[4] `^` d14);
    t.[5] <- VPSLLV_4u64 state.[4] rhotates_left_p.[3];
    state.[4] <- VPSRLV_4u64 state.[4] rhotates_right_p.[3];
    state.[4] <- (state.[4] `|` t.[5]);
    state.[5] <- (state.[5] `^` d14);
    t.[6] <- VPSLLV_4u64 state.[5] rhotates_left_p.[4];
    state.[5] <- VPSRLV_4u64 state.[5] rhotates_right_p.[4];
    state.[5] <- (state.[5] `|` t.[6]);
    state.[6] <- (state.[6] `^` d14);
    t.[3] <- VPERMQ state.[2]
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    t.[4] <- VPERMQ state.[3]
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    t.[7] <- VPSLLV_4u64 state.[6] rhotates_left_p.[5];
    t.[1] <- VPSRLV_4u64 state.[6] rhotates_right_p.[5];
    t.[1] <- (t.[1] `|` t.[7]);
    state.[1] <- (state.[1] `^` d14);
    t.[5] <- VPERMQ state.[4]
    (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    t.[6] <- VPERMQ state.[5]
    (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
    t.[8] <- VPSLLV_4u64 state.[1] rhotates_left_p.[1];
    t.[2] <- VPSRLV_4u64 state.[1] rhotates_right_p.[1];
    t.[2] <- (t.[2] `|` t.[8]);
    t.[7] <- VPSRLDQ_256 t.[1] (W8.of_int 8);
    t.[0] <- ((invw t.[1]) `&` t.[7]);
    state.[3] <- VPBLEND_8u32 t.[2] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[8] <- VPBLEND_8u32 t.[4] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[5] <- VPBLEND_8u32 t.[3] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[7] <- VPBLEND_8u32 t.[2] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[3] <- VPBLEND_8u32 state.[3] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[8] <- VPBLEND_8u32 t.[8] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[5] <- VPBLEND_8u32 state.[5] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[7] <- VPBLEND_8u32 t.[7] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[3] <- VPBLEND_8u32 state.[3] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t.[8] <- VPBLEND_8u32 t.[8] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[5] <- VPBLEND_8u32 state.[5] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t.[7] <- VPBLEND_8u32 t.[7] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[3] <- ((invw state.[3]) `&` t.[8]);
    state.[5] <- ((invw state.[5]) `&` t.[7]);
    state.[6] <- VPBLEND_8u32 t.[5] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[8] <- VPBLEND_8u32 t.[3] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[3] <- (state.[3] `^` t.[3]);
    state.[6] <- VPBLEND_8u32 state.[6] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[8] <- VPBLEND_8u32 t.[8] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[5] <- (state.[5] `^` t.[5]);
    state.[6] <- VPBLEND_8u32 state.[6] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t.[8] <- VPBLEND_8u32 t.[8] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[6] <- ((invw state.[6]) `&` t.[8]);
    state.[6] <- (state.[6] `^` t.[6]);
    state.[4] <- VPERMQ t.[1]
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    t.[8] <- VPBLEND_8u32 state.[4] state.[0]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[1] <- VPERMQ t.[1]
    (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    state.[1] <- VPBLEND_8u32 state.[1] state.[0]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[1] <- ((invw state.[1]) `&` t.[8]);
    state.[2] <- VPBLEND_8u32 t.[4] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[7] <- VPBLEND_8u32 t.[6] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[2] <- VPBLEND_8u32 state.[2] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[7] <- VPBLEND_8u32 t.[7] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[2] <- VPBLEND_8u32 state.[2] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t.[7] <- VPBLEND_8u32 t.[7] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[2] <- ((invw state.[2]) `&` t.[7]);
    state.[2] <- (state.[2] `^` t.[2]);
    t.[0] <- VPERMQ t.[0]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    state.[3] <- VPERMQ state.[3]
    (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    state.[5] <- VPERMQ state.[5]
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    state.[6] <- VPERMQ state.[6]
    (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
    state.[4] <- VPBLEND_8u32 t.[6] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[7] <- VPBLEND_8u32 t.[5] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[4] <- VPBLEND_8u32 state.[4] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t.[7] <- VPBLEND_8u32 t.[7] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    state.[4] <- VPBLEND_8u32 state.[4] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t.[7] <- VPBLEND_8u32 t.[7] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[4] <- ((invw state.[4]) `&` t.[7]);
    state.[0] <- (state.[0] `^` t.[0]);
    state.[1] <- (state.[1] `^` t.[1]);
    state.[4] <- (state.[4] `^` t.[4]);
    state.[0] <-
    (state.[0] `^` (get256_direct
                   (WArray768.init256 (fun i => (iotas_p).[i]))
                   (W64.to_uint iotas_o)));
    iotas_o <- (iotas_o + (W64.of_int 32));
    ( _0,  _1,  _2, zf, r) <- DEC_64 r;
    while ((! zf)) {
      c00 <- VPSHUFD_256 state.[2]
      (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
      c14 <- (state.[5] `^` state.[3]);
      t.[2] <- (state.[4] `^` state.[6]);
      c14 <- (c14 `^` state.[1]);
      c14 <- (c14 `^` t.[2]);
      t.[4] <- VPERMQ c14
      (W8.of_int (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
      c00 <- (c00 `^` state.[2]);
      t.[0] <- VPERMQ c00
      (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
      t.[1] <- (c14 \vshr64u256 (W8.of_int 63));
      t.[2] <- (c14 \vadd64u256 c14);
      t.[1] <- (t.[1] `|` t.[2]);
      d14 <- VPERMQ t.[1]
      (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      d00 <- (t.[1] `^` t.[4]);
      d00 <- VPERMQ d00
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      c00 <- (c00 `^` state.[0]);
      c00 <- (c00 `^` t.[0]);
      t.[0] <- (c00 \vshr64u256 (W8.of_int 63));
      t.[1] <- (c00 \vadd64u256 c00);
      t.[1] <- (t.[1] `|` t.[0]);
      state.[2] <- (state.[2] `^` d00);
      state.[0] <- (state.[0] `^` d00);
      d14 <- VPBLEND_8u32 d14 t.[1]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      t.[4] <- VPBLEND_8u32 t.[4] c00
      (W8.of_int (1 %% 2^1 +
                 2^1 * (1 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      d14 <- (d14 `^` t.[4]);
      t.[3] <- VPSLLV_4u64 state.[2] rhotates_left_p.[0];
      state.[2] <- VPSRLV_4u64 state.[2] rhotates_right_p.[0];
      state.[2] <- (state.[2] `|` t.[3]);
      state.[3] <- (state.[3] `^` d14);
      t.[4] <- VPSLLV_4u64 state.[3] rhotates_left_p.[2];
      state.[3] <- VPSRLV_4u64 state.[3] rhotates_right_p.[2];
      state.[3] <- (state.[3] `|` t.[4]);
      state.[4] <- (state.[4] `^` d14);
      t.[5] <- VPSLLV_4u64 state.[4] rhotates_left_p.[3];
      state.[4] <- VPSRLV_4u64 state.[4] rhotates_right_p.[3];
      state.[4] <- (state.[4] `|` t.[5]);
      state.[5] <- (state.[5] `^` d14);
      t.[6] <- VPSLLV_4u64 state.[5] rhotates_left_p.[4];
      state.[5] <- VPSRLV_4u64 state.[5] rhotates_right_p.[4];
      state.[5] <- (state.[5] `|` t.[6]);
      state.[6] <- (state.[6] `^` d14);
      t.[3] <- VPERMQ state.[2]
      (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
      t.[4] <- VPERMQ state.[3]
      (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
      t.[7] <- VPSLLV_4u64 state.[6] rhotates_left_p.[5];
      t.[1] <- VPSRLV_4u64 state.[6] rhotates_right_p.[5];
      t.[1] <- (t.[1] `|` t.[7]);
      state.[1] <- (state.[1] `^` d14);
      t.[5] <- VPERMQ state.[4]
      (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
      t.[6] <- VPERMQ state.[5]
      (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
      t.[8] <- VPSLLV_4u64 state.[1] rhotates_left_p.[1];
      t.[2] <- VPSRLV_4u64 state.[1] rhotates_right_p.[1];
      t.[2] <- (t.[2] `|` t.[8]);
      t.[7] <- VPSRLDQ_256 t.[1] (W8.of_int 8);
      t.[0] <- ((invw t.[1]) `&` t.[7]);
      state.[3] <- VPBLEND_8u32 t.[2] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[8] <- VPBLEND_8u32 t.[4] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[5] <- VPBLEND_8u32 t.[3] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[7] <- VPBLEND_8u32 t.[2] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[3] <- VPBLEND_8u32 state.[3] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[8] <- VPBLEND_8u32 t.[8] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[5] <- VPBLEND_8u32 state.[5] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[7] <- VPBLEND_8u32 t.[7] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[3] <- VPBLEND_8u32 state.[3] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      t.[8] <- VPBLEND_8u32 t.[8] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      state.[5] <- VPBLEND_8u32 state.[5] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      t.[7] <- VPBLEND_8u32 t.[7] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      state.[3] <- ((invw state.[3]) `&` t.[8]);
      state.[5] <- ((invw state.[5]) `&` t.[7]);
      state.[6] <- VPBLEND_8u32 t.[5] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[8] <- VPBLEND_8u32 t.[3] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[3] <- (state.[3] `^` t.[3]);
      state.[6] <- VPBLEND_8u32 state.[6] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[8] <- VPBLEND_8u32 t.[8] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[5] <- (state.[5] `^` t.[5]);
      state.[6] <- VPBLEND_8u32 state.[6] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      t.[8] <- VPBLEND_8u32 t.[8] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      state.[6] <- ((invw state.[6]) `&` t.[8]);
      state.[6] <- (state.[6] `^` t.[6]);
      state.[4] <- VPERMQ t.[1]
      (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
      t.[8] <- VPBLEND_8u32 state.[4] state.[0]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[1] <- VPERMQ t.[1]
      (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      state.[1] <- VPBLEND_8u32 state.[1] state.[0]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      state.[1] <- ((invw state.[1]) `&` t.[8]);
      state.[2] <- VPBLEND_8u32 t.[4] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[7] <- VPBLEND_8u32 t.[6] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[2] <- VPBLEND_8u32 state.[2] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[7] <- VPBLEND_8u32 t.[7] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[2] <- VPBLEND_8u32 state.[2] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      t.[7] <- VPBLEND_8u32 t.[7] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      state.[2] <- ((invw state.[2]) `&` t.[7]);
      state.[2] <- (state.[2] `^` t.[2]);
      t.[0] <- VPERMQ t.[0]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      state.[3] <- VPERMQ state.[3]
      (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
      state.[5] <- VPERMQ state.[5]
      (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
      state.[6] <- VPERMQ state.[6]
      (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
      state.[4] <- VPBLEND_8u32 t.[6] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[7] <- VPBLEND_8u32 t.[5] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[4] <- VPBLEND_8u32 state.[4] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      t.[7] <- VPBLEND_8u32 t.[7] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      state.[4] <- VPBLEND_8u32 state.[4] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      t.[7] <- VPBLEND_8u32 t.[7] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      state.[4] <- ((invw state.[4]) `&` t.[7]);
      state.[0] <- (state.[0] `^` t.[0]);
      state.[1] <- (state.[1] `^` t.[1]);
      state.[4] <- (state.[4] `^` t.[4]);
      state.[0] <-
      (state.[0] `^` (get256_direct
                     (WArray768.init256 (fun i => (iotas_p).[i]))
                     (W64.to_uint iotas_o)));
      iotas_o <- (iotas_o + (W64.of_int 32));
      ( _0,  _1,  _2, zf, r) <- DEC_64 r;
    }
    return (state);
  }
  
  proc comp_u64_l_int_and_u64_l_int (a:W64.t, b:int, c:W64.t, d:int) : 
  bool = {
    
    var c3:bool;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var c1:bool;
    var bc1:W8.t;
    var c2:bool;
    var bc2:W8.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_) <- CMP_64 a (W64.of_int b);
    c1 <- (_uLT _of_ _cf_ _sf_ _zf_);
    bc1 <- SETcc c1;
    (_of_, _cf_, _sf_,  _1, _zf_) <- CMP_64 c (W64.of_int d);
    c2 <- (_uLT _of_ _cf_ _sf_ _zf_);
    bc2 <- SETcc c2;
    (_of_, _cf_, _sf_,  _2, _zf_) <- TEST_8 bc1 bc2;
    c3 <- (_NEQ _of_ _cf_ _sf_ _zf_);
    return (c3);
  }
  
  proc _4u64x4_u256x4 (y0:W256.t, y1:W256.t, y2:W256.t, y3:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    
    x0 <- VPERM2I128 y0 y2 (W8.of_int 32);
    x1 <- VPERM2I128 y1 y3 (W8.of_int 32);
    x2 <- VPERM2I128 y0 y2 (W8.of_int 49);
    x3 <- VPERM2I128 y1 y3 (W8.of_int 49);
    y0 <- VPUNPCKL_4u64 x0 x1;
    y1 <- VPUNPCKH_4u64 x0 x1;
    y2 <- VPUNPCKL_4u64 x2 x3;
    y3 <- VPUNPCKH_4u64 x2 x3;
    return (y0, y1, y2, y3);
  }
  
  proc __st4x_unpack_at (buf:W64.t Array272.t, st4x:W256.t Array25.t,
                         offset:W64.t) : W64.t Array272.t = {
    var aux: int;
    
    var i:int;
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    
    i <- 0;
    while (i < 6) {
      x0 <- st4x.[((4 * i) + 0)];
      x1 <- st4x.[((4 * i) + 1)];
      x2 <- st4x.[((4 * i) + 2)];
      x3 <- st4x.[((4 * i) + 3)];
      (x0, x1, x2, x3) <@ _4u64x4_u256x4 (x0, x1, x2, x3);
      buf <-
      Array272.init
      (WArray2176.get64 (WArray2176.set256_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int ((4 * 8) * i))) + (W64.of_int ((0 * 8) * (((3 * 21) + 4) + 1))))) (x0)));
      buf <-
      Array272.init
      (WArray2176.get64 (WArray2176.set256_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int ((4 * 8) * i))) + (W64.of_int ((1 * 8) * (((3 * 21) + 4) + 1))))) (x1)));
      buf <-
      Array272.init
      (WArray2176.get64 (WArray2176.set256_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int ((4 * 8) * i))) + (W64.of_int ((2 * 8) * (((3 * 21) + 4) + 1))))) (x2)));
      buf <-
      Array272.init
      (WArray2176.get64 (WArray2176.set256_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int ((4 * 8) * i))) + (W64.of_int ((3 * 8) * (((3 * 21) + 4) + 1))))) (x3)));
      i <- i + 1;
    }
    t0 <-
    (get64 (WArray800.init256 (fun i_0 => (st4x).[i_0])) ((4 * 24) + 0));
    t1 <-
    (get64 (WArray800.init256 (fun i_0 => (st4x).[i_0])) ((4 * 24) + 1));
    t2 <-
    (get64 (WArray800.init256 (fun i_0 => (st4x).[i_0])) ((4 * 24) + 2));
    t3 <-
    (get64 (WArray800.init256 (fun i_0 => (st4x).[i_0])) ((4 * 24) + 3));
    buf <-
    Array272.init
    (WArray2176.get64 (WArray2176.set64_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int (8 * 24))) + (W64.of_int ((0 * 8) * (((3 * 21) + 4) + 1))))) (t0)));
    buf <-
    Array272.init
    (WArray2176.get64 (WArray2176.set64_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int (8 * 24))) + (W64.of_int ((1 * 8) * (((3 * 21) + 4) + 1))))) (t1)));
    buf <-
    Array272.init
    (WArray2176.get64 (WArray2176.set64_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int (8 * 24))) + (W64.of_int ((2 * 8) * (((3 * 21) + 4) + 1))))) (t2)));
    buf <-
    Array272.init
    (WArray2176.get64 (WArray2176.set64_direct (WArray2176.init64 (fun i_0 => (buf).[i_0])) (W64.to_uint ((offset + (W64.of_int (8 * 24))) + (W64.of_int ((3 * 8) * (((3 * 21) + 4) + 1))))) (t3)));
    return (buf);
  }
  
  proc __stavx2_pack_at (st:W64.t Array68.t, offset:W64.t) : W256.t Array7.t = {
    
    var state:W256.t Array7.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    var r:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    state <- witness;
    state.[0] <-
    VPBROADCAST_4u64 (get64_direct (WArray544.init64 (fun i => (st).[i]))
                     (W64.to_uint ((W64.of_int (8 * 0)) + offset)));
    state.[1] <-
    (get256_direct (WArray544.init64 (fun i => (st).[i]))
    (W64.to_uint ((W64.of_int (1 * 8)) + offset)));
    t128_0 <-
    VMOV_64 (get64_direct (WArray544.init64 (fun i => (st).[i]))
            (W64.to_uint ((W64.of_int (5 * 8)) + offset)));
    state.[3] <-
    (get256_direct (WArray544.init64 (fun i => (st).[i]))
    (W64.to_uint ((W64.of_int (6 * 8)) + offset)));
    t128_1 <-
    VMOV_64 (get64_direct (WArray544.init64 (fun i => (st).[i]))
            (W64.to_uint ((W64.of_int (10 * 8)) + offset)));
    state.[4] <-
    (get256_direct (WArray544.init64 (fun i => (st).[i]))
    (W64.to_uint ((W64.of_int (11 * 8)) + offset)));
    r <-
    (get64_direct (WArray544.init64 (fun i => (st).[i]))
    (W64.to_uint ((W64.of_int (15 * 8)) + offset)));
    t128_0 <- VPINSR_2u64 t128_0 r (W8.of_int 1);
    state.[5] <-
    (get256_direct (WArray544.init64 (fun i => (st).[i]))
    (W64.to_uint ((W64.of_int (16 * 8)) + offset)));
    r <-
    (get64_direct (WArray544.init64 (fun i => (st).[i]))
    (W64.to_uint ((W64.of_int (20 * 8)) + offset)));
    t128_1 <- VPINSR_2u64 t128_1 r (W8.of_int 1);
    state.[2] <-
    (W256.of_int ((W128.to_uint t128_1) %% 2^128 +
                 2^128 * (W128.to_uint t128_0)));
    state.[6] <-
    (get256_direct (WArray544.init64 (fun i => (st).[i]))
    (W64.to_uint ((W64.of_int (21 * 8)) + offset)));
    t256_0 <- VPBLEND_8u32 state.[3] state.[5]
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t256_1 <- VPBLEND_8u32 state.[6] state.[4]
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t256_2 <- VPBLEND_8u32 state.[4] state.[3]
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[3] <- VPBLEND_8u32 t256_0 t256_1
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[4] <- VPBLEND_8u32 t256_1 t256_0
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t256_0 <- VPBLEND_8u32 state.[5] state.[6]
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[5] <- VPBLEND_8u32 t256_0 t256_2
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    state.[6] <- VPBLEND_8u32 t256_2 t256_0
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    return (state);
  }
  
  proc _stavx2_pack_at (st:W64.t Array68.t, offset:W64.t) : W256.t Array7.t = {
    
    var stavx2:W256.t Array7.t;
    stavx2 <- witness;
    stavx2 <@ __stavx2_pack_at (st, offset);
    return (stavx2);
  }
  
  proc __stavx2_unpack_at (buf:W64.t Array68.t, offset:W64.t,
                           state:W256.t Array7.t) : W64.t Array68.t = {
    
    var t128_0:W128.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t128_1:W128.t;
    var t256_4:W256.t;
    
    t128_0 <- (truncateu128 state.[0]);
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set64_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (0 * 8)) + offset)) (VMOVLPD t128_0)));
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set256_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (1 * 8)) + offset)) (
    state.[1])));
    t256_0 <- VPBLEND_8u32 state.[3] state.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t256_1 <- VPBLEND_8u32 state.[4] state.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t256_2 <- VPBLEND_8u32 state.[5] state.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t256_3 <- VPBLEND_8u32 state.[6] state.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t128_1 <- VEXTRACTI128 state.[2] (W8.of_int 1);
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set64_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (5 * 8)) + offset)) (VMOVLPD t128_1)));
    t256_4 <- VPBLEND_8u32 t256_0 t256_3
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set256_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (6 * 8)) + offset)) (t256_4)));
    t128_0 <- (truncateu128 state.[2]);
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set64_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (10 * 8)) + offset)) (VMOVLPD t128_0)));
    t256_4 <- VPBLEND_8u32 t256_3 t256_1
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set256_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (11 * 8)) + offset)) (t256_4)));
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set64_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (15 * 8)) + offset)) (VMOVHPD t128_1)));
    t256_4 <- VPBLEND_8u32 t256_2 t256_0
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set256_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (16 * 8)) + offset)) (t256_4)));
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set64_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (20 * 8)) + offset)) (VMOVHPD t128_0)));
    t256_4 <- VPBLEND_8u32 t256_1 t256_2
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    buf <-
    Array68.init
    (WArray544.get64 (WArray544.set256_direct (WArray544.init64 (fun i => (buf).[i])) (W64.to_uint ((W64.of_int (21 * 8)) + offset)) (t256_4)));
    return (buf);
  }
  
  proc _stavx2_unpack_at (buf:W64.t Array68.t, offset:W64.t,
                          state:W256.t Array7.t) : W64.t Array68.t = {
    
    
    
    buf <@ __stavx2_unpack_at (buf, offset, state);
    return (buf);
  }
  
  proc xof_init_x4 (rho:W8.t Array32.t, indexes:W16.t Array4.t) : W256.t Array25.t = {
    var aux: int;
    
    var state:W256.t Array25.t;
    var i:int;
    var t:W256.t;
    var r:W64.t;
    var temp:W256.t Array1.t;
    state <- witness;
    temp <- witness;
    i <- 0;
    while (i < 4) {
      t <-
      VPBROADCAST_4u64 (get64 (WArray32.init8 (fun i_0 => (rho).[i_0])) i);
      state.[i] <- t;
      i <- i + 1;
    }
    i <- 0;
    while (i < 4) {
      r <- (zeroextu64 indexes.[i]);
      r <- (r `|` (W64.of_int 2031616));
      temp <-
      Array1.init
      (WArray32.get256 (WArray32.set64 (WArray32.init256 (fun i_0 => (temp).[i_0])) i (r)));
      i <- i + 1;
    }
    t <- temp.[0];
    state.[4] <- t;
    t <- set0_256 ;
    i <- 5;
    while (i < 25) {
      state.[i] <- t;
      i <- i + 1;
    }
    t <- RATE_BIT_x4.[0];
    t <- (t `^` state.[20]);
    state.[20] <- t;
    return (state);
  }
  
  proc xof_init_avx2 (rho:W8.t Array32.t, index:W16.t) : W256.t Array7.t = {
    var aux: int;
    
    var state:W256.t Array7.t;
    var r:W64.t;
    var temp:W256.t Array1.t;
    var t:W256.t;
    var t128:W128.t;
    var i:int;
    state <- witness;
    temp <- witness;
    state.[0] <-
    VPBROADCAST_4u64 (get64 (WArray32.init8 (fun i_0 => (rho).[i_0])) 0);
    r <- (get64 (WArray32.init8 (fun i_0 => (rho).[i_0])) 1);
    temp <-
    Array1.init
    (WArray32.get256 (WArray32.set64 (WArray32.init256 (fun i_0 => (temp).[i_0])) 0 (r)));
    r <- (get64 (WArray32.init8 (fun i_0 => (rho).[i_0])) 2);
    temp <-
    Array1.init
    (WArray32.get256 (WArray32.set64 (WArray32.init256 (fun i_0 => (temp).[i_0])) 1 (r)));
    r <- (get64 (WArray32.init8 (fun i_0 => (rho).[i_0])) 3);
    temp <-
    Array1.init
    (WArray32.get256 (WArray32.set64 (WArray32.init256 (fun i_0 => (temp).[i_0])) 2 (r)));
    r <- (zeroextu64 index);
    r <- (r `|` (W64.of_int 2031616));
    temp <-
    Array1.init
    (WArray32.get256 (WArray32.set64 (WArray32.init256 (fun i_0 => (temp).[i_0])) 3 (r)));
    state.[1] <- temp.[0];
    t <- set0_256 ;
    t128 <- (truncateu128 t);
    r <- (W64.of_int 9223372036854775808);
    state.[2] <- zeroextu256(VPINSR_2u64 t128 r (W8.of_int 1));
    i <- 3;
    while (i < 7) {
      state.[i] <- t;
      i <- i + 1;
    }
    return (state);
  }
  
  proc __gen_matrix_buf_rejection_filter48 (pol:W16.t Array256.t,
                                            counter:W64.t,
                                            buf:W64.t Array68.t,
                                            buf_offset:W64.t,
                                            load_shuffle:W256.t, mask:W256.t,
                                            bounds:W256.t,
                                            sst:W8.t Array2048.t,
                                            ones:W256.t, ms:W64.t) : 
  W16.t Array256.t * W64.t = {
    
    var f0:W256.t;
    var f1:W256.t;
    var g0:W256.t;
    var g1:W256.t;
    var good:W64.t;
    var t0_0:W64.t;
    var shuffle_0:W256.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var t0_1:W64.t;
    var shuffle_0_1:W128.t;
    var t1_0:W64.t;
    var shuffle_1:W256.t;
    var t1_1:W64.t;
    var shuffle_1_1:W128.t;
    var shuffle_t:W256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    f0 <-
    VPERMQ (get256_direct (WArray544.init64 (fun i => (buf).[i]))
           ((W64.to_uint buf_offset) + 0))
    (W8.of_int (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
    f1 <-
    VPERMQ (get256_direct (WArray544.init64 (fun i => (buf).[i]))
           ((W64.to_uint buf_offset) + 24))
    (W8.of_int (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
    f0 <- VPSHUFB_256 f0 load_shuffle;
    f1 <- VPSHUFB_256 f1 load_shuffle;
    g0 <- VPSRL_16u16 f0 (W8.of_int 4);
    g1 <- VPSRL_16u16 f1 (W8.of_int 4);
    f0 <- VPBLEND_16u16 f0 g0 (W8.of_int 170);
    f1 <- VPBLEND_16u16 f1 g1 (W8.of_int 170);
    f0 <- VPAND_256 f0 mask;
    f1 <- VPAND_256 f1 mask;
    g0 <- VPCMPGT_16u16 bounds f0;
    g1 <- VPCMPGT_16u16 bounds f1;
    g0 <- VPACKSS_16u16 g0 g1;
    good <- VPMOVMSKB_u256u64 g0;
    good <- protect_64 good ms;
    t0_0 <- good;
    t0_0 <- (t0_0 `&` (W64.of_int 255));
    shuffle_0 <-
    zeroextu256(VMOV_64 (get64 (WArray2048.init8 (fun i => (sst).[i]))
                        (W64.to_uint t0_0)));
    (_of_, _cf_, _sf_,  _0, _zf_, t0_0) <- POPCNT_64 t0_0;
    t0_0 <- (t0_0 + counter);
    t0_1 <- good;
    t0_1 <- (t0_1 `>>` (W8.of_int 16));
    t0_1 <- (t0_1 `&` (W64.of_int 255));
    shuffle_0_1 <-
    VMOV_64 (get64 (WArray2048.init8 (fun i => (sst).[i]))
            (W64.to_uint t0_1));
    (_of_, _cf_, _sf_,  _1, _zf_, t0_1) <- POPCNT_64 t0_1;
    t0_1 <- (t0_1 + t0_0);
    t1_0 <- good;
    t1_0 <- (t1_0 `>>` (W8.of_int 8));
    t1_0 <- (t1_0 `&` (W64.of_int 255));
    shuffle_1 <-
    zeroextu256(VMOV_64 (get64 (WArray2048.init8 (fun i => (sst).[i]))
                        (W64.to_uint t1_0)));
    (_of_, _cf_, _sf_,  _2, _zf_, t1_0) <- POPCNT_64 t1_0;
    t1_0 <- (t1_0 + t0_1);
    t1_1 <- good;
    t1_1 <- (t1_1 `>>` (W8.of_int 24));
    t1_1 <- (t1_1 `&` (W64.of_int 255));
    shuffle_1_1 <-
    VMOV_64 (get64 (WArray2048.init8 (fun i => (sst).[i]))
            (W64.to_uint t1_1));
    (_of_, _cf_, _sf_,  _3, _zf_, t1_1) <- POPCNT_64 t1_1;
    t1_1 <- (t1_1 + t1_0);
    shuffle_0 <- VINSERTI128 shuffle_0 shuffle_0_1 (W8.of_int 1);
    shuffle_1 <- VINSERTI128 shuffle_1 shuffle_1_1 (W8.of_int 1);
    shuffle_t <- VPADD_32u8 shuffle_0 ones;
    shuffle_0 <- VPUNPCKL_32u8 shuffle_0 shuffle_t;
    shuffle_t <- VPADD_32u8 shuffle_1 ones;
    shuffle_1 <- VPUNPCKL_32u8 shuffle_1 shuffle_t;
    f0 <- VPSHUFB_256 f0 shuffle_0;
    f1 <- VPSHUFB_256 f1 shuffle_1;
    pol <-
    Array256.init
    (WArray512.get16 (WArray512.set128_direct (WArray512.init16 (fun i => (pol).[i])) (W64.to_uint ((W64.of_int 2) * counter)) ((truncateu128 f0))));
    pol <-
    Array256.init
    (WArray512.get16 (WArray512.set128_direct (WArray512.init16 (fun i => (pol).[i])) (W64.to_uint ((W64.of_int 2) * t0_0)) (VEXTRACTI128 f0
    (W8.of_int 1))));
    pol <-
    Array256.init
    (WArray512.get16 (WArray512.set128_direct (WArray512.init16 (fun i => (pol).[i])) (W64.to_uint ((W64.of_int 2) * t0_1)) ((truncateu128 f1))));
    pol <-
    Array256.init
    (WArray512.get16 (WArray512.set128_direct (WArray512.init16 (fun i => (pol).[i])) (W64.to_uint ((W64.of_int 2) * t1_0)) (VEXTRACTI128 f1
    (W8.of_int 1))));
    counter <- t1_1;
    return (pol, counter);
  }
  
  proc __write_u128_boundchk (pol:W16.t Array256.t, ctr:W64.t, data:W128.t,
                              ms:W64.t) : W16.t Array256.t * W64.t * W64.t = {
    
    var condition_8:bool;
    var data_u64:W64.t;
    var condition_4:bool;
    var condition_2:bool;
    var condition_1:bool;
    
    condition_8 <- (ctr \ule (W64.of_int (256 - 8)));
    if (condition_8) {
      ms <- update_msf condition_8 ms;
      pol <-
      Array256.init
      (WArray512.get16 (WArray512.set128_direct (WArray512.init16 (fun i => (pol).[i])) (2 * (W64.to_uint ctr)) (data)));
      ctr <- (ctr + (W64.of_int 8));
    } else {
      ms <- update_msf (! condition_8) ms;
      data_u64 <- MOVV_64 (truncateu64 data);
      condition_4 <- (ctr \ule (W64.of_int (256 - 4)));
      if (condition_4) {
        ms <- update_msf condition_4 ms;
        pol <-
        Array256.init
        (WArray512.get16 (WArray512.set64_direct (WArray512.init16 (fun i => (pol).[i])) (2 * (W64.to_uint ctr)) (data_u64)));
        data_u64 <- VPEXTR_64 data (W8.of_int 1);
        ctr <- (ctr + (W64.of_int 4));
      } else {
        ms <- update_msf (! condition_4) ms;
      }
      condition_2 <- (ctr \ule (W64.of_int (256 - 2)));
      if (condition_2) {
        ms <- update_msf condition_2 ms;
        pol <-
        Array256.init
        (WArray512.get16 (WArray512.set32_direct (WArray512.init16 (fun i => (pol).[i])) (2 * (W64.to_uint ctr)) ((truncateu32 data_u64))));
        data_u64 <- (data_u64 `>>` (W8.of_int 32));
        ctr <- (ctr + (W64.of_int 2));
      } else {
        ms <- update_msf (! condition_2) ms;
      }
      condition_1 <- (ctr \ule (W64.of_int (256 - 1)));
      if (condition_1) {
        ms <- update_msf condition_1 ms;
        pol <-
        Array256.init
        (WArray512.get16 (WArray512.set16_direct (WArray512.init16 (fun i => (pol).[i])) (2 * (W64.to_uint ctr)) ((truncateu16 data_u64))));
        ctr <- (ctr + (W64.of_int 1));
      } else {
        ms <- update_msf (! condition_1) ms;
      }
    }
    return (pol, ctr, ms);
  }
  
  proc __gen_matrix_buf_rejection_filter24 (pol:W16.t Array256.t,
                                            counter:W64.t,
                                            buf:W64.t Array68.t,
                                            buf_offset:W64.t,
                                            load_shuffle:W256.t, mask:W256.t,
                                            bounds:W256.t,
                                            sst:W8.t Array2048.t,
                                            ones:W256.t, ms:W64.t) : 
  W16.t Array256.t * W64.t * W64.t = {
    
    var f0:W256.t;
    var g0:W256.t;
    var g1:W256.t;
    var good:W64.t;
    var t0_0:W64.t;
    var shuffle_0:W256.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var t0_1:W64.t;
    var shuffle_0_1:W128.t;
    var shuffle_t:W256.t;
    var t128:W128.t;
    var  _0:bool;
    var  _1:bool;
    
    f0 <-
    VPERMQ (get256_direct (WArray544.init64 (fun i => (buf).[i]))
           ((W64.to_uint buf_offset) + 0))
    (W8.of_int (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
    f0 <- VPSHUFB_256 f0 load_shuffle;
    g0 <- VPSRL_16u16 f0 (W8.of_int 4);
    f0 <- VPBLEND_16u16 f0 g0 (W8.of_int 170);
    f0 <- VPAND_256 f0 mask;
    g0 <- VPCMPGT_16u16 bounds f0;
    g1 <- set0_256 ;
    g0 <- VPACKSS_16u16 g0 g1;
    good <- VPMOVMSKB_u256u64 g0;
    good <- protect_64 good ms;
    t0_0 <- good;
    t0_0 <- (t0_0 `&` (W64.of_int 255));
    shuffle_0 <-
    zeroextu256(VMOV_64 (get64 (WArray2048.init8 (fun i => (sst).[i]))
                        (W64.to_uint t0_0)));
    (_of_, _cf_, _sf_,  _0, _zf_, t0_0) <- POPCNT_64 t0_0;
    t0_0 <- (t0_0 + counter);
    t0_1 <- good;
    t0_1 <- (t0_1 `>>` (W8.of_int 16));
    t0_1 <- (t0_1 `&` (W64.of_int 255));
    shuffle_0_1 <-
    VMOV_64 (get64 (WArray2048.init8 (fun i => (sst).[i]))
            (W64.to_uint t0_1));
    (_of_, _cf_, _sf_,  _1, _zf_, t0_1) <- POPCNT_64 t0_1;
    t0_1 <- (t0_1 + t0_0);
    shuffle_0 <- VINSERTI128 shuffle_0 shuffle_0_1 (W8.of_int 1);
    shuffle_t <- VPADD_32u8 shuffle_0 ones;
    shuffle_0 <- VPUNPCKL_32u8 shuffle_0 shuffle_t;
    f0 <- VPSHUFB_256 f0 shuffle_0;
    t128 <- (truncateu128 f0);
    (pol, counter, ms) <@ __write_u128_boundchk (pol, counter, t128, ms);
    t128 <- VEXTRACTI128 f0 (W8.of_int 1);
    (pol, counter, ms) <@ __write_u128_boundchk (pol, t0_0, t128, ms);
    counter <- t0_1;
    return (pol, counter, ms);
  }
  
  proc _gen_matrix_buf_rejection (pol:W16.t Array256.t, counter:W64.t,
                                  buf:W64.t Array68.t, buf_offset:W64.t) : 
  W16.t Array256.t * W64.t = {
    
    var ms:W64.t;
    var load_shuffle:W256.t;
    var mask:W256.t;
    var bounds:W256.t;
    var ones:W256.t;
    var sst:W8.t Array2048.t;
    var condition_loop:bool;
    sst <- witness;
    ms <- init_msf ;
    load_shuffle <-
    (get256 (WArray32.init8 (fun i => (sample_load_shuffle).[i])) 0);
    mask <- sample_mask;
    bounds <- sample_q;
    ones <- sample_ones;
    sst <- sample_shuffle_table;
    buf_offset <- buf_offset;
    condition_loop <@ comp_u64_l_int_and_u64_l_int (buf_offset,
    (((3 * 168) - 48) + 1), counter, ((256 - 32) + 1));
    while (condition_loop) {
      ms <- update_msf condition_loop ms;
      (pol, counter) <@ __gen_matrix_buf_rejection_filter48 (pol, counter,
      buf, buf_offset, load_shuffle, mask, bounds, sst, ones, ms);
      buf_offset <- (buf_offset + (W64.of_int 48));
      condition_loop <@ comp_u64_l_int_and_u64_l_int (buf_offset,
      (((3 * 168) - 48) + 1), counter, ((256 - 32) + 1));
    }
    ms <- update_msf (! condition_loop) ms;
    condition_loop <@ comp_u64_l_int_and_u64_l_int (buf_offset,
    (((3 * 168) - 24) + 1), counter, (256 + 1));
    while (condition_loop) {
      ms <- update_msf condition_loop ms;
      (pol, counter, ms) <@ __gen_matrix_buf_rejection_filter24 (pol,
      counter, buf, buf_offset, load_shuffle, mask, bounds, sst, ones, ms);
      buf_offset <- (buf_offset + (W64.of_int 24));
      condition_loop <@ comp_u64_l_int_and_u64_l_int (buf_offset,
      (((3 * 168) - 24) + 1), counter, (256 + 1));
    }
    return (pol, counter);
  }
  
  proc gen_matrix_get_indexes (b:W64.t, _t:W64.t) : W16.t Array4.t = {
    
    var idx:W16.t Array4.t;
    var gmi:W16.t Array16.t;
    var t:W64.t;
    gmi <- witness;
    idx <- witness;
    gmi <- gen_matrix_indexes;
    t <- _t;
    t <- (t `<<` (W8.of_int 3));
    b <- (b + t);
    idx.[0] <- gmi.[((W64.to_uint b) + 0)];
    idx.[1] <- gmi.[((W64.to_uint b) + 1)];
    idx.[2] <- gmi.[((W64.to_uint b) + 2)];
    idx.[3] <- gmi.[((W64.to_uint b) + 3)];
    return (idx);
  }
  
  proc _gen_matrix_sample_four_polynomials (polx4:W16.t Array1024.t,
                                            bufx4:W64.t Array272.t,
                                            rho:W8.t Array32.t,
                                            mat_entry:W64.t, transposed:W64.t) : 
  W16.t Array1024.t * W64.t Array272.t = {
    var aux: int;
    
    var indexes:W16.t Array4.t;
    var state:W256.t Array25.t;
    var stx4:W256.t Array25.t;
    var buf_offset:W64.t;
    var i:int;
    var buf:W64.t Array68.t;
    var pol:W16.t Array256.t;
    var counter:W64.t;
    var stavx2:W256.t Array7.t;
    buf <- witness;
    indexes <- witness;
    pol <- witness;
    state <- witness;
    stavx2 <- witness;
    stx4 <- witness;
    indexes <@ gen_matrix_get_indexes (mat_entry, transposed);
    state <@ xof_init_x4 (rho, indexes);
    stx4 <- state;
    buf_offset <- (W64.of_int 0);
    
    while ((buf_offset \ult (W64.of_int (3 * 168)))) {
      stx4 <@ _keccakf1600_4x (stx4);
      bufx4 <@ __st4x_unpack_at (bufx4, stx4, buf_offset);
      buf_offset <- (buf_offset + (W64.of_int 168));
    }
    i <- 0;
    while (i < 4) {
      buf <-
      (Array68.init (fun i_0 => bufx4.[(i * (((3 * 21) + 4) + 1)) + i_0]));
      buf_offset <- (W64.of_int 0);
      pol <- (Array256.init (fun i_0 => polx4.[(i * 256) + i_0]));
      counter <- (W64.of_int 0);
      (pol, counter) <@ _gen_matrix_buf_rejection (pol, counter, buf,
      buf_offset);
      buf_offset <- (W64.of_int (2 * 168));
      
      while ((counter \ult (W64.of_int 256))) {
        stavx2 <@ _stavx2_pack_at (buf, buf_offset);
        stavx2 <@ _keccakf1600_avx2 (stavx2);
        buf <@ _stavx2_unpack_at (buf, buf_offset, stavx2);
        (pol, counter) <@ _gen_matrix_buf_rejection (pol, counter, buf,
        buf_offset);
      }
      polx4 <- Array1024.init
               (fun i_0 => if (i * 256) <= i_0 < (i * 256) + 256
               then pol.[i_0-(i * 256)] else polx4.[i_0]);
      bufx4 <- Array272.init
               (fun i_0 => if (i * (((3 * 21) + 4) + 1)) <= i_0 < (i * (((3 * 21) + 4) + 1)) + 68
               then buf.[i_0-(i * (((3 * 21) + 4) + 1))] else bufx4.[i_0]);
      i <- i + 1;
    }
    return (polx4, bufx4);
  }
  
  proc __gen_matrix_sample_one_polynomial (pol:W16.t Array256.t,
                                           buf:W64.t Array68.t,
                                           rho:W8.t Array32.t, rc:W16.t) : 
  W16.t Array256.t * W64.t Array68.t = {
    
    var stavx2:W256.t Array7.t;
    var buf_offset:W64.t;
    var counter:W64.t;
    stavx2 <- witness;
    stavx2 <@ xof_init_avx2 (rho, rc);
    buf_offset <- (W64.of_int 0);
    
    while ((buf_offset \ult (W64.of_int (3 * 168)))) {
      stavx2 <@ _keccakf1600_avx2 (stavx2);
      buf <@ _stavx2_unpack_at (buf, buf_offset, stavx2);
      buf_offset <- (buf_offset + (W64.of_int 168));
    }
    buf_offset <- (W64.of_int 0);
    counter <- (W64.of_int 0);
    (pol, counter) <@ _gen_matrix_buf_rejection (pol, counter, buf,
    buf_offset);
    buf_offset <- (W64.of_int (2 * 168));
    
    while ((counter \ult (W64.of_int 256))) {
      stavx2 <@ _stavx2_pack_at (buf, buf_offset);
      stavx2 <@ _keccakf1600_avx2 (stavx2);
      buf <@ _stavx2_unpack_at (buf, buf_offset, stavx2);
      (pol, counter) <@ _gen_matrix_buf_rejection (pol, counter, buf,
      buf_offset);
    }
    return (pol, buf);
  }
  
  proc _gen_matrix_avx2 (matrix:W16.t Array2304.t, rho:W8.t Array32.t,
                         transposed:W64.t) : W16.t Array2304.t = {
    var aux: int;
    var aux_0: W16.t Array256.t;
    
    var bufx4_s:W64.t Array272.t;
    var bufx4:W64.t Array272.t;
    var i:int;
    var mat_entry:W64.t;
    var polx4:W16.t Array1024.t;
    var buf:W64.t Array68.t;
    var pol:W16.t Array256.t;
    var rc:W16.t;
    var j:int;
    var  _0:W64.t Array68.t;
     _0 <- witness;
    buf <- witness;
    bufx4 <- witness;
    bufx4_s <- witness;
    pol <- witness;
    polx4 <- witness;
    (* Erased call to spill *)
    bufx4 <- bufx4_s;
    i <- 0;
    while (i < 2) {
      mat_entry <- (W64.of_int (4 * i));
      polx4 <- (Array1024.init (fun i_0 => matrix.[((4 * i) * 256) + i_0]));
      (* Erased call to unspill *)
      (polx4, bufx4) <@ _gen_matrix_sample_four_polynomials (polx4, bufx4,
      rho, mat_entry, transposed);
      matrix <- Array2304.init
                (fun i_0 => if ((i * 4) * 256) <= i_0 < ((i * 4) * 256) + 1024
                then polx4.[i_0-((i * 4) * 256)] else matrix.[i_0]);
      i <- i + 1;
    }
    buf <- (Array68.init (fun i_0 => bufx4.[0 + i_0]));
    pol <- (Array256.init (fun i_0 => matrix.[(8 * 256) + i_0]));
    rc <- (W16.of_int 514);
    (pol,  _0) <@ __gen_matrix_sample_one_polynomial (pol, buf, rho, rc);
    matrix <- Array2304.init
              (fun i_0 => if (8 * 256) <= i_0 < (8 * 256) + 256
              then pol.[i_0-(8 * 256)] else matrix.[i_0]);
    bufx4_s <- bufx4;
    i <- 0;
    while (i < 3) {
      j <- 0;
      while (j < 3) {
        aux_0 <@ _nttunpack ((Array256.init (fun i_0 => matrix.[((i * (3 * 256)) + (j * 256)) + i_0])));
        matrix <- Array2304.init
                  (fun i_0 => if ((i * (3 * 256)) + (j * 256)) <= i_0 < ((i * (3 * 256)) + (j * 256)) + 256
                  then aux_0.[i_0-((i * (3 * 256)) + (j * 256))]
                  else matrix.[i_0]);
        j <- j + 1;
      }
      i <- i + 1;
    }
    return (matrix);
  }
  
  proc __indcpa_keypair (pkp:W64.t, skp:W64.t, randomnessp:W8.t Array32.t) : unit = {
    var aux: int;
    var aux_3: W16.t Array256.t;
    var aux_2: W16.t Array256.t;
    var aux_1: W16.t Array256.t;
    var aux_0: W16.t Array256.t;
    
    var i:int;
    var t64:W64.t;
    var inbuf:W8.t Array32.t;
    var buf:W8.t Array64.t;
    var publicseed:W8.t Array32.t;
    var noiseseed:W8.t Array32.t;
    var transposed:W64.t;
    var aa:W16.t Array2304.t;
    var nonce:W8.t;
    var skpv:W16.t Array768.t;
    var e:W16.t Array768.t;
    var pkpv:W16.t Array768.t;
    aa <- witness;
    buf <- witness;
    e <- witness;
    inbuf <- witness;
    noiseseed <- witness;
    pkpv <- witness;
    publicseed <- witness;
    skpv <- witness;
    (* Erased call to spill *)
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => (randomnessp).[i_0])) i);
      inbuf <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => (inbuf).[i_0])) i (t64)));
      i <- i + 1;
    }
    buf <@ _sha3_512_32 (buf, inbuf);
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray64.init8 (fun i_0 => (buf).[i_0])) i);
      publicseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => (publicseed).[i_0])) i (t64)));
      t64 <-
      (get64 (WArray64.init8 (fun i_0 => (buf).[i_0])) (i + (32 %/ 8)));
      noiseseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => (noiseseed).[i_0])) i (t64)));
      i <- i + 1;
    }
    transposed <- (W64.of_int 0);
    aa <@ _gen_matrix_avx2 (aa, publicseed, transposed);
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
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_2.[i_0-256]
            else skpv.[i_0]);
    skpv <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux_1.[i_0-(2 * 256)] else skpv.[i_0]);
    e <- Array768.init
         (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_0.[i_0-0] else e.[i_0]);
    nonce <- (W8.of_int 4);
    (aux_3, aux_2, aux_1,
    aux_0) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => e.[256 + i_0])),
    (Array256.init (fun i_0 => e.[(2 * 256) + i_0])),
    (Array256.init (fun i_0 => pkpv.[0 + i_0])),
    (Array256.init (fun i_0 => pkpv.[256 + i_0])), noiseseed, nonce);
    e <- Array768.init
         (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_3.[i_0-256]
         else e.[i_0]);
    e <- Array768.init
         (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
         then aux_2.[i_0-(2 * 256)] else e.[i_0]);
    pkpv <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_1.[i_0-0]
            else pkpv.[i_0]);
    pkpv <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_0.[i_0-256]
            else pkpv.[i_0]);
    skpv <@ __polyvec_ntt (skpv);
    e <@ __polyvec_ntt (e);
    i <- 0;
    while (i < 3) {
      aux_3 <@ __polyvec_pointwise_acc ((Array256.init (fun i_0 => pkpv.[(i * 256) + i_0])),
      (Array768.init (fun i_0 => aa.[(i * (3 * 256)) + i_0])), skpv);
      pkpv <- Array768.init
              (fun i_0 => if (i * 256) <= i_0 < (i * 256) + 256
              then aux_3.[i_0-(i * 256)] else pkpv.[i_0]);
      aux_3 <@ _poly_frommont ((Array256.init (fun i_0 => pkpv.[(i * 256) + i_0])));
      pkpv <- Array768.init
              (fun i_0 => if (i * 256) <= i_0 < (i * 256) + 256
              then aux_3.[i_0-(i * 256)] else pkpv.[i_0]);
      i <- i + 1;
    }
    pkpv <@ __polyvec_add2 (pkpv, e);
    pkpv <@ __polyvec_reduce (pkpv);
    (* Erased call to unspill *)
    __polyvec_tobytes (skp, skpv);
    __polyvec_tobytes (pkp, pkpv);
    pkp <- (pkp + (W64.of_int (3 * 384)));
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => (publicseed).[i_0])) i);
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (pkp + (W64.of_int 0))) (t64);
      pkp <- (pkp + (W64.of_int 8));
      i <- i + 1;
    }
    return ();
  }
  
  proc __indcpa_enc_0 (sctp:W64.t, msgp:W8.t Array32.t, pkp:W64.t,
                       noiseseed:W8.t Array32.t) : unit = {
    var aux_3: int;
    var aux_2: W16.t Array256.t;
    var aux_1: W16.t Array256.t;
    var aux_0: W16.t Array256.t;
    var aux: W16.t Array256.t;
    
    var pkpv:W16.t Array768.t;
    var i:W64.t;
    var t64:W64.t;
    var publicseed:W8.t Array32.t;
    var k:W16.t Array256.t;
    var s_noiseseed:W8.t Array32.t;
    var transposed:W64.t;
    var aat:W16.t Array2304.t;
    var lnoiseseed:W8.t Array32.t;
    var nonce:W8.t;
    var sp_0:W16.t Array768.t;
    var ep:W16.t Array768.t;
    var epp:W16.t Array256.t;
    var bp:W16.t Array768.t;
    var w:int;
    var v:W16.t Array256.t;
    var ctp:W64.t;
    aat <- witness;
    bp <- witness;
    ep <- witness;
    epp <- witness;
    k <- witness;
    lnoiseseed <- witness;
    pkpv <- witness;
    publicseed <- witness;
    s_noiseseed <- witness;
    sp_0 <- witness;
    v <- witness;
    pkpv <@ __polyvec_frombytes (pkp);
    i <- (W64.of_int 0);
    pkp <- (pkp + (W64.of_int (3 * 384)));
    
    while ((i \ult (W64.of_int (32 %/ 8)))) {
      t64 <- (loadW64 Glob.mem (W64.to_uint (pkp + (W64.of_int 0))));
      publicseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64_direct (WArray32.init8 (fun i_0 => (publicseed).[i_0])) (8 * (W64.to_uint i)) (t64)));
      pkp <- (pkp + (W64.of_int 8));
      i <- (i + (W64.of_int 1));
    }
    k <@ _poly_frommsg_1 (k, msgp);
    s_noiseseed <- noiseseed;
    transposed <- (W64.of_int 1);
    aat <@ _gen_matrix_avx2 (aat, publicseed, transposed);
    lnoiseseed <- s_noiseseed;
    nonce <- (W8.of_int 0);
    (aux_2, aux_1, aux_0,
    aux) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => sp_0.[0 + i_0])),
    (Array256.init (fun i_0 => sp_0.[256 + i_0])),
    (Array256.init (fun i_0 => sp_0.[(2 * 256) + i_0])),
    (Array256.init (fun i_0 => ep.[0 + i_0])), lnoiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_2.[i_0-0]
            else sp_0.[i_0]);
    sp_0 <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_1.[i_0-256]
            else sp_0.[i_0]);
    sp_0 <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux_0.[i_0-(2 * 256)] else sp_0.[i_0]);
    ep <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else ep.[i_0]);
    nonce <- (W8.of_int 4);
    (aux_2, aux_1, aux_0,
    aux) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => ep.[256 + i_0])),
    (Array256.init (fun i_0 => ep.[(2 * 256) + i_0])), epp,
    (Array256.init (fun i_0 => bp.[0 + i_0])), lnoiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_2.[i_0-256]
          else ep.[i_0]);
    ep <- Array768.init
          (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
          then aux_1.[i_0-(2 * 256)] else ep.[i_0]);
    epp <- aux_0;
    bp <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else bp.[i_0]);
    sp_0 <@ __polyvec_ntt (sp_0);
    w <- 0;
    while (w < 3) {
      aux_2 <@ __polyvec_pointwise_acc ((Array256.init (fun i_0 => bp.[(w * 256) + i_0])),
      (Array768.init (fun i_0 => aat.[(w * (3 * 256)) + i_0])), sp_0);
      bp <- Array768.init
            (fun i_0 => if (w * 256) <= i_0 < (w * 256) + 256
            then aux_2.[i_0-(w * 256)] else bp.[i_0]);
      w <- w + 1;
    }
    v <@ __polyvec_pointwise_acc (v, pkpv, sp_0);
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
  
  proc __indcpa_enc_1 (ctp:W8.t Array1088.t, msgp:W8.t Array32.t, pkp:W64.t,
                       noiseseed:W8.t Array32.t) : W8.t Array1088.t = {
    var aux_3: int;
    var aux_5: W8.t Array128.t;
    var aux_4: W8.t Array960.t;
    var aux_2: W16.t Array256.t;
    var aux_1: W16.t Array256.t;
    var aux_0: W16.t Array256.t;
    var aux: W16.t Array256.t;
    
    var pkpv:W16.t Array768.t;
    var i:W64.t;
    var t64:W64.t;
    var publicseed:W8.t Array32.t;
    var k:W16.t Array256.t;
    var s_noiseseed:W8.t Array32.t;
    var transposed:W64.t;
    var aat:W16.t Array2304.t;
    var lnoiseseed:W8.t Array32.t;
    var nonce:W8.t;
    var sp_0:W16.t Array768.t;
    var ep:W16.t Array768.t;
    var epp:W16.t Array256.t;
    var bp:W16.t Array768.t;
    var w:int;
    var v:W16.t Array256.t;
    aat <- witness;
    bp <- witness;
    ep <- witness;
    epp <- witness;
    k <- witness;
    lnoiseseed <- witness;
    pkpv <- witness;
    publicseed <- witness;
    s_noiseseed <- witness;
    sp_0 <- witness;
    v <- witness;
    pkpv <@ __polyvec_frombytes (pkp);
    i <- (W64.of_int 0);
    pkp <- (pkp + (W64.of_int (3 * 384)));
    
    while ((i \ult (W64.of_int (32 %/ 8)))) {
      t64 <- (loadW64 Glob.mem (W64.to_uint (pkp + (W64.of_int 0))));
      publicseed <-
      Array32.init
      (WArray32.get8 (WArray32.set64_direct (WArray32.init8 (fun i_0 => (publicseed).[i_0])) (8 * (W64.to_uint i)) (t64)));
      pkp <- (pkp + (W64.of_int 8));
      i <- (i + (W64.of_int 1));
    }
    k <@ _poly_frommsg_1 (k, msgp);
    s_noiseseed <- noiseseed;
    transposed <- (W64.of_int 1);
    aat <@ _gen_matrix_avx2 (aat, publicseed, transposed);
    lnoiseseed <- s_noiseseed;
    nonce <- (W8.of_int 0);
    (aux_2, aux_1, aux_0,
    aux) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => sp_0.[0 + i_0])),
    (Array256.init (fun i_0 => sp_0.[256 + i_0])),
    (Array256.init (fun i_0 => sp_0.[(2 * 256) + i_0])),
    (Array256.init (fun i_0 => ep.[0 + i_0])), lnoiseseed, nonce);
    sp_0 <- Array768.init
            (fun i_0 => if 0 <= i_0 < 0 + 256 then aux_2.[i_0-0]
            else sp_0.[i_0]);
    sp_0 <- Array768.init
            (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_1.[i_0-256]
            else sp_0.[i_0]);
    sp_0 <- Array768.init
            (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
            then aux_0.[i_0-(2 * 256)] else sp_0.[i_0]);
    ep <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else ep.[i_0]);
    nonce <- (W8.of_int 4);
    (aux_2, aux_1, aux_0,
    aux) <@ _poly_getnoise_eta1_4x ((Array256.init (fun i_0 => ep.[256 + i_0])),
    (Array256.init (fun i_0 => ep.[(2 * 256) + i_0])), epp,
    (Array256.init (fun i_0 => bp.[0 + i_0])), lnoiseseed, nonce);
    ep <- Array768.init
          (fun i_0 => if 256 <= i_0 < 256 + 256 then aux_2.[i_0-256]
          else ep.[i_0]);
    ep <- Array768.init
          (fun i_0 => if (2 * 256) <= i_0 < (2 * 256) + 256
          then aux_1.[i_0-(2 * 256)] else ep.[i_0]);
    epp <- aux_0;
    bp <- Array768.init
          (fun i_0 => if 0 <= i_0 < 0 + 256 then aux.[i_0-0] else bp.[i_0]);
    sp_0 <@ __polyvec_ntt (sp_0);
    w <- 0;
    while (w < 3) {
      aux_2 <@ __polyvec_pointwise_acc ((Array256.init (fun i_0 => bp.[(w * 256) + i_0])),
      (Array768.init (fun i_0 => aat.[(w * (3 * 256)) + i_0])), sp_0);
      bp <- Array768.init
            (fun i_0 => if (w * 256) <= i_0 < (w * 256) + 256
            then aux_2.[i_0-(w * 256)] else bp.[i_0]);
      w <- w + 1;
    }
    v <@ __polyvec_pointwise_acc (v, pkpv, sp_0);
    bp <@ __polyvec_invntt (bp);
    v <@ _poly_invntt (v);
    bp <@ __polyvec_add2 (bp, ep);
    v <@ _poly_add2 (v, epp);
    v <@ _poly_add2 (v, k);
    bp <@ __polyvec_reduce (bp);
    v <@ __poly_reduce (v);
    aux_4 <@ __polyvec_compress_1 ((Array960.init (fun i_0 => ctp.[0 + i_0])),
    bp);
    ctp <- Array1088.init
           (fun i_0 => if 0 <= i_0 < 0 + 960 then aux_4.[i_0-0]
           else ctp.[i_0]);
    (aux_5,
    aux_2) <@ _poly_compress_1 ((Array128.init (fun i_0 => ctp.[(3 * 320) + i_0])),
    v);
    ctp <- Array1088.init
           (fun i_0 => if (3 * 320) <= i_0 < (3 * 320) + 128
           then aux_5.[i_0-(3 * 320)] else ctp.[i_0]);
    v <- aux_2;
    return (ctp);
  }
  
  proc __indcpa_dec_1 (msgp:W8.t Array32.t, ctp:W64.t, skp:W64.t) : W8.t Array32.t = {
    
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
    t <@ __polyvec_pointwise_acc (t, skpv, bp);
    t <@ _poly_invntt (t);
    mp <@ _poly_sub (mp, v, t);
    mp <@ __poly_reduce (mp);
    (msgp, mp) <@ _poly_tomsg_1 (msgp, mp);
    return (msgp);
  }
  
  proc __verify (ctp:W64.t, ctpc:W8.t Array1088.t) : W64.t = {
    var aux: int;
    
    var cnd:W64.t;
    var t64:W64.t;
    var h:W256.t;
    var i:int;
    var f:W256.t;
    var g:W256.t;
    var zf:bool;
    var off:int;
    var t1:W8.t;
    var t2:W8.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    cnd <- (W64.of_int 0);
    t64 <- (W64.of_int 1);
    h <- set0_256 ;
    aux <- (((3 * 320) + 128) %/ 32);
    i <- 0;
    while (i < aux) {
      f <-
      (get256_direct (WArray1088.init8 (fun i_0 => (ctpc).[i_0])) (32 * i));
      g <- (loadW256 Glob.mem (W64.to_uint (ctp + (W64.of_int (32 * i)))));
      f <- VPXOR_256 f g;
      h <- VPOR_256 h f;
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf) <- VPTEST_256 h h;
    cnd <- ((! zf) ? t64 : cnd);
    off <- ((((3 * 320) + 128) %/ 32) * 32);
    aux <- ((3 * 320) + 128);
    i <- off;
    while (i < aux) {
      t1 <- (get8_direct (WArray1088.init8 (fun i_0 => (ctpc).[i_0])) i);
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
    
    var scnd:W64.t;
    var m:W256.t;
    var i:int;
    var f:W256.t;
    var g:W256.t;
    var off:int;
    var bcond:W8.t;
    var t2:W8.t;
    var t1:W8.t;
    
    cnd <- (- cnd);
    scnd <- cnd;
    m <- VPBROADCAST_4u64 scnd;
    aux <- (32 %/ 32);
    i <- 0;
    while (i < aux) {
      f <-
      (get256_direct (WArray32.init8 (fun i_0 => (src).[i_0])) (32 * i));
      g <- (loadW256 Glob.mem (W64.to_uint (dst + (W64.of_int (32 * i)))));
      f <- VPBLENDVB_256 f g m;
      Glob.mem <-
      storeW256 Glob.mem (W64.to_uint (dst + (W64.of_int (32 * i)))) (f);
      i <- i + 1;
    }
    off <- ((32 %/ 32) * 32);
    bcond <- (truncateu8 cnd);
    i <- off;
    while (i < 32) {
      t2 <- (loadW8 Glob.mem (W64.to_uint (dst + (W64.of_int i))));
      t1 <- src.[i];
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
      t64 <- (loadW64 Glob.mem (W64.to_uint (pkp + (W64.of_int (8 * i)))));
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int 0))) (t64);
      skp <- (skp + (W64.of_int 8));
      i <- i + 1;
    }
    s_skp <- skp;
    pkp <- s_pkp;
    t64 <- (W64.of_int ((3 * 384) + 32));
    h_pk <@ _isha3_256 (h_pk, pkp, t64);
    skp <- s_skp;
    i <- 0;
    while (i < 4) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => (h_pk).[i_0])) i);
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int 0))) (t64);
      skp <- (skp + (W64.of_int 8));
      i <- i + 1;
    }
    randomnessp <- s_randomnessp;
    randomnessp2 <- (Array32.init (fun i_0 => randomnessp.[32 + i_0]));
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => (randomnessp2).[i_0])) i);
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int 0))) (t64);
      skp <- (skp + (W64.of_int 8));
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
      t64 <- (get64 (WArray32.init8 (fun i_0 => (randomnessp).[i_0])) i);
      buf <-
      Array64.init
      (WArray64.get8 (WArray64.set64 (WArray64.init8 (fun i_0 => (buf).[i_0])) i (t64)));
      i <- i + 1;
    }
    t64 <- (W64.of_int ((3 * 384) + 32));
    aux_0 <@ _isha3_256 ((Array32.init (fun i_0 => buf.[32 + i_0])), pkp,
    t64);
    buf <- Array64.init
           (fun i_0 => if 32 <= i_0 < 32 + 32 then aux_0.[i_0-32]
           else buf.[i_0]);
    kr <@ _sha3_512_64 (kr, buf);
    pkp <- s_pkp;
    __indcpa_enc_0 (s_ctp, (Array32.init (fun i_0 => buf.[0 + i_0])), pkp,
    (Array32.init (fun i_0 => kr.[32 + i_0])));
    shkp <- s_shkp;
    aux <- (32 %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray64.init8 (fun i_0 => (kr).[i_0])) i);
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
    aux <@ __indcpa_dec_1 ((Array32.init (fun i_0 => buf.[0 + i_0])), ctp,
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
      (WArray64.get8 (WArray64.set64_direct (WArray64.init8 (fun i_0 => (buf).[i_0])) (32 + (8 * i)) (t64)));
      i <- i + 1;
    }
    s_skp <- skp;
    kr <@ _sha3_512_64 (kr, buf);
    pkp <- s_skp;
    pkp <- (pkp + (W64.of_int (((12 * 3) * 256) `|>>` 3)));
    ctpc <@ __indcpa_enc_1 (ctpc, (Array32.init (fun i_0 => buf.[0 + i_0])),
    pkp, (Array32.init (fun i_0 => kr.[32 + i_0])));
    ctp <- s_ctp;
    cnd <@ __verify (ctp, ctpc);
    s_cnd <- cnd;
    ctp <- s_ctp;
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
  
  proc jade_kem_mlkem_mlkem768_amd64_avx2_keypair (public_key:W64.t,
                                                   secret_key:W64.t) : 
  W64.t = {
    
    var r:W64.t;
    var randomness:W8.t Array64.t;
    var randomnessp:W8.t Array64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
    randomness <- witness;
    randomnessp <- witness;
    public_key <- public_key;
    secret_key <- secret_key;
    randomnessp <- randomness;
    randomnessp <@ SC.randombytes_64 (randomnessp);
     _0 <- init_msf ;
    __crypto_kem_keypair_jazz (public_key, secret_key, randomnessp);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- set0_64 ;
    return (r);
  }
  
  proc jade_kem_mlkem_mlkem768_amd64_avx2_enc (ciphertext:W64.t,
                                               shared_secret:W64.t,
                                               public_key:W64.t) : W64.t = {
    
    var r:W64.t;
    var randomness:W8.t Array32.t;
    var randomnessp:W8.t Array32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
    randomness <- witness;
    randomnessp <- witness;
    ciphertext <- ciphertext;
    shared_secret <- shared_secret;
    public_key <- public_key;
    randomnessp <- randomness;
    randomnessp <@ SC.randombytes_32 (randomnessp);
     _0 <- init_msf ;
    __crypto_kem_enc_jazz (ciphertext, shared_secret, public_key,
    randomnessp);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- set0_64 ;
    return (r);
  }
  
  proc jade_kem_mlkem_mlkem768_amd64_avx2_dec (shared_secret:W64.t,
                                               ciphertext:W64.t,
                                               secret_key:W64.t) : W64.t = {
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
    
     _0 <- init_msf ;
    __crypto_kem_dec_jazz (shared_secret, ciphertext, secret_key);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- set0_64 ;
    return (r);
  }
}.

