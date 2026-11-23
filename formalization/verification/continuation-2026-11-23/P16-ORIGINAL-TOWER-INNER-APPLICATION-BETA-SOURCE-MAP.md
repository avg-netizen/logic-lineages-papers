# Paper 16: exact first beta of the printed inner map at a real native index

Correspondence: Paper 16 `sections/ordinals.tex` lines 535–553 (the inner
iterator formula (B_T) and literal terminal Z), and 569–590 (native tower
family). The source is the exact substituted `innerMap l` from the checked
`NativeTowerIndexedEntryTargets`, not the outer omega index application.

`NativeTowerInnerMapSubstitutionProof` establishes lookup in the actual
nearest-first consumed outer binder block, then uses the existing literal
block substitution law on the inner expression. Discharging its sole index
binder exposes the original level-l iterator with the actual closed outer
arguments, followed by the entire descending literal suffix ending in Z at
every nonempty suffix. At l=0, Z is the iterator's real seed. The same proof
also handles the unrestricted raw j syntax in the *substitution equality*
only; the actual native beta theorem requires a genuinely closed native
j of original indexType and the exact literal map identity. It proves actual
raw Reduction and original NativeBelow in this first step.

The next root will handle the three precise iterator steps under those
function slots. No whole-symbolic iterator realization, semantics, rank,
or height assertion is made by either literal equation or first beta.
