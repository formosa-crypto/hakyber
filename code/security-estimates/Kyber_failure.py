import operator as op
from math import factorial as fac
from math import sqrt, log
import sys
from proba_util import *

def p2_cyclotomic_final_error_distribution(ps):
    """ construct the final error distribution in our encryption scheme
    :param ps: parameter set (ParameterSet)
    """
    chis = build_centered_binomial_law(ps.ks)           # LWE error law for the key
    chie = build_centered_binomial_law(ps.ke)           # LWE error law for the ciphertext
    Rk = build_mod_switching_error_law(ps.q, ps.rqk)    # Rounding error public key
    Rc = build_mod_switching_error_law(ps.q, ps.rqc)    # rounding error first ciphertext
    chiRs = chis # law_convolution(chis, Rk)            # LWE $ +Rounding error key
    chiRe = law_convolution(chie, Rc)                   # LWE + rounding error ciphertext

    B1 = law_product(chie, chiRs)                       # (LWE+Rounding error) * LWE (as in a E*S product)
    B2 = law_product(chis, chiRe)
    # B1 => ei[i] * s[i]
    # B2 => s[i] * (ei[i] + cu[i]) = (s[i] * ei[i]) + (s[i] * cu[i])
    C1 = iter_law_convolution(B1, ps.m * ps.n)
    C2 = iter_law_convolution(B2, ps.m * ps.n)

    C=law_convolution(C1, C2)

    R2 = build_mod_switching_error_law(ps.q, ps.rq2)    # Rounding2 (in the ciphertext mask part)
    F = law_convolution(R2, chie)                       # LWE+Rounding2 error
    D = law_convolution(C, F)                           # Final error
    DwithoutR2 = law_convolution(C, chie)               # Final error without R2
    return (D,DwithoutR2)


def p2_cyclotomic_error_probability(ps):
    (D,DwithoutR2) = p2_cyclotomic_final_error_distribution(ps)
    e = worst_mod_switching_error(ps.q,ps.rq2)
    print ("Worst case v error: "+ str(e))
    proba = tail_probability(D, ps.q/4)
    probaWithoutR2 = tail_probability(DwithoutR2, ps.q/4 - e)
    return D, ps.n*proba, DwithoutR2, ps.n*probaWithoutR2


