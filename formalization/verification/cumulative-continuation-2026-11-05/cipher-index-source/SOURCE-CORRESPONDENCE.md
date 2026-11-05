# Actual index cipher

## Scope

Target-only native preflight passed before proof authoring. All four exact
aliases passed the first bounded native proof gate, with only standard axioms.
The five-file package characterizes and represents the actual sequence
0,1,...,n-1 in the original sparse encoding. See `CIPHER-INDEX-ACCEPTANCE.json`.
Its 36-module local import closure has current source hashes matched to successful
native receipts.

The definitions retain base r=2^(4q), sparse positions 2^(i+1), the domain
n+1<q, all natural inputs, and n=0. No validity premise is assumed for an
arbitrary number satisfying the arithmetic recurrence. Validity is derived
from equality with the actual index encoding. No stronger n+2<q bound is used.

## Exact arithmetic characterization

Write I=encode n q id, U=ones n q, V=shiftedOnes n q, P=r^(2^(n+1)).
The frozen arithmetic target is

    (n+1<q and a=I)
      iff
    (n+1<q and ((a*U) AND ((r-1)*V))+V=a+n*P).

For the actual I, the accepted product-mask theorem gives the shifted index
encoding. A finite-sum identity adds the increment V. Conversely U is even,
so multiplication by U raises binary congruence precision by one bit. Fixed
AND masks preserve congruence, and the linear equality forces uniqueness.
This is the linear counterpart of the checked sparse-ones contraction.

The variable-input Diophantine proof existentially supplies U,V from the
checked original OnesDiophantine relation, then uses arithmetic, exponentiation
and the checked natural AND graph. The source CodeNat relation is exactly
IsCipherOf n q id a and follows without a new premise.

## Primary-source correspondence

https://github.com/uds-psl/H10-LMCS-v1.1/blob/c2586aee45cf60e7fb8b112ac701b02d7dc3cfeb/theories/H10/Matija/cipher.v

- Lines 1215–1218: actual cipher semantics.
- Lines 1551–1668: CodeNat and IncSeq_dio_priv.
- Lines 1670–1695: CodeNat_dio.
- Dio/dio_cipher.v lines 68–76: dio_rel_CodeNat.

The source uses an auxiliary z and valid-cipher witnesses. Its second equation
reduces to z=a+U by the already checked ones shift relation r²+V=U+P. The
shorter frozen equation eliminates that auxiliary. Its converse is an
alternative exact uniqueness proof, not a literal transcription or an
assumption that arbitrary candidate inputs are valid ciphers.

## Still pending

Elementary-system normalization, full variable bounded-universal closure,
ordinary recursion/minimization graph cases, the universal evaluator,
computable polynomial specialization, RE reductions, and MRDP/undecidability
remain unproved by this package.
