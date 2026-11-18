# Independent final same-carrier marking/free typing review

Accepted eight frozen endpoints. Independently reran read-only
verify_spine_marking.py:11 modules,8 aliases,zero errors. All frozen pins,
source/dependency inputs, compiler context, output bundles, native receipt/log
hashes match; actual alias closures standard-only. Native final receipt
1794978112227898425-2. No reviewer compiler run.

Read final FreeTypingProof and SpineMarkingProof. prefixLookup proves the
actual shifted index lookup under a finite binder prefix; prefixCompatible
is derived internally, not passed to the endpoint. Structural free typing
lifts typed outside images, extends the prefix under lambdas, and preserves
original base/extras typing. Empty-prefix specialization is literal depth0.
Marking proofs preserve existing marked owners exactly, transport typing
through original lambdas, and use success to eliminate variable-ended spines.
Raw success-only covariance maps bases/extras without a hidden image-shape
premise. Failed marking is not claimed to commute.

Frozen source/targets unchanged. Reported repair is confined to proof
indentation/name inference, with failed proof retained. These laws establish
same-carrier marking and concrete typed free transport, not named alpha
correspondence or actual weak/strict ordering closure. No numbered theorem,
full-root build or CI completion claimed.
