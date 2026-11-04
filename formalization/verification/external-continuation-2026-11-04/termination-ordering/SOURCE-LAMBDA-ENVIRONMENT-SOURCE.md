# Typed environments for a later applicative-body lambda theorem

Source paper06 lines620–622: structural computable substitution; lines582–597: lambda instances. This is an environment/identity prerequisite only, not lambda computability.

ArgumentEnvironment extends theta by here mapped to an explicitly supplied confined computable argument a and there mapped to theta. Guarded GoodSubstitution and pointwise computability are separate premises/conclusions. This elementary case split works for arbitrary semantic P and does not need a decoded context or scalar calibration; it makes no assertion that the chosen symbols/window correspond to the context code.

FreshEnvironment instead uses actual liftSubstitution theta, mapping here to the existing fresh variable and there to weakened theta images. Successful Context decoding, SubtypeClosed, sigma membership and fresh-context scalar calibration are explicit. Computability of every weakened theta image is explicitly supplied in that fresh context. Existing-variable computability supplies the here case, while accepted liftGood supplies guarded literal confinement. No old-to-new semantic computability transport is inferred.

ExtendedBetaIdentity is literal typed syntax equality: beta-instantiating the lifted substitution of body equals substituting the extended argument environment. It follows from accepted substitution composition and substitution-through-weakening cancellation, with full typed contexts/binder retained. It holds for arbitrary body syntax; the later use will restrict body to ApplicativeFragment.

No lambda computability theorem, general C weakening, all-term preservation, precedence/rewrite WF or ID1 derivation. Proof absent pending review/freeze; no export.
