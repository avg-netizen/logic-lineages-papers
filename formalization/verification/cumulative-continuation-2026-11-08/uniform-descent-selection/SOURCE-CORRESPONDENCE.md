# Original uniform descent selection

The input tuple contains exactly the four binary Programs selected by
`InternalOriginalUniformParameterLeaves`. It is chosen after the ranked
signature n/arity and before symbols, the finite type window S, ambient Gamma,
and precedence table. No correctness or closure theorem is stored as data.
The runtime parameter remains the original pair of contextCode and encoded
Gamma; all original leaf codecs and malformed-input defaults are unchanged.

The new source and target validators are literal specializations of
`InternalParameterizedApplicationValidityFold.sourceP` and `targetP`.
Source validity is the exact target/universe conjunction. Every requested
original parameter slice is calibrated on all natural packed values.

The selected representative D runs the existing parameterized bounded descent
B precisely when the source validator returns one; otherwise it retains the
original packed-target representative R. The source-valid proof consumes
original least-code minimality, source validity of the representative, its
original outer type and idempotence. B uses input+1 steps and carries the
identical parameter. The fallback preserves malformed values and decoded
nonuniverse values without introducing a target-universe filter.

The ternary typed checker takes [value, requestedType, parameter]. Its actual
AST checks requested-type membership, source validity, the original left
field, and T(value,parameter)=value. Original carrier characterization and
membership establish all-input equality to the original canonical typed
carrier at every encoded source context, assuming only the original
subtype-closed-window condition for canonical descent.

Internal targets use arbitrary binary leaves, positive bodies, contexts,
symbolic values, type codes and parameters. They derive the typed factors,
output validity/type/transition-fixedness, typed output under explicit
requested-type membership, and source closure for the original application
constructor. Child successful runs and semantic calibration are not premises.
No numerical evaluation equality becomes an internal graph equality.

The selection target proves one Data tuple with both all-input leaf
calibration and all internal laws before universally quantifying the source
contexts. It does not identify the later canonical result fold, prove uniform
edge/path correctness, remove the argument-fiber restriction, or finish the
unqualified CertifiedApplicationLift or paper06 lem:id1.
