# Actual alpha renaming preserves all-environment encoding

Frozen EncodeRespectsAlpha passed native checking in `1794980720522192424-2`.
Read-only verifier reconciles eight modules, one exact alias and zero errors.
Only propext/Quot.sound. Original core profile and frozen definitions unchanged.

The proof derives concrete name lookup append/position/equality laws, then
encoding agreement for every name occurring in a raw named term. Actual
capture-safe free renaming is proved to preserve encoding with the renamed
binder under arbitrary local and outside typed-name environments. A shadowing
binder uses the environment agreement theorem, not an assumed alpha law.
Finally the generated full Alpha/AlphaArgs recursor handles equivalence closure,
structural congruence and the independently defined fresh-renaming generator.

Failed draft `1794980672602794850-2` retained. Proof repairs split remaining
Option cases for lookup arithmetic, infer variable names after equality
elimination, normalize the shadowed binder, and use the generated full mutual
recursor. Diagnostic receipt `1794980696571022031-2` retained outside production.
One unused-simp warning remains; it does not affect checked closure.

Converse AlphaExact, named decode/encode alpha roundtrip, OpeningBridge and
comparison derivation transport remain unproved. No full alpha characterization,
numbered manuscript theorem, root build or CI claim.
