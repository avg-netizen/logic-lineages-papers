# Parameter-preserving dominant-boundary projection

This packet targets the concrete no-wide-interval case in Snyatkov 2008, printed pp44–45, toward paper08 thm:snyatkov. The original PDF at /tmp/l3-snyatkov-2008.pdf has SHA256 13f5ef161fa40d1bd24de131a0cbe450e9a51cf5a4b9514f5ee48bd2deb8019e. It is a reading aid, not an import.

For a positive coefficient a, a dominant summand sigma=a*Phi(x+e) and a row s between one half and three halves of sigma imply 2*lower<=3*a*Phi(x+e) and a*Phi(x+e)<=2*upper. At the original floor-inverse-selected positive crossing c=phiInverse((2*lower-1)/a)+1, failure of a wide interval gives 2*upper<3*a*Phi(c+1). The actual Phi doubling bound over two steps yields x+e in [c-2,c+2]. The packet emits exactly five literal candidate substitutions and retains every original predicate and domain in every branch.

The lower and upper endpoints are arbitrary expanded terms independent of the eliminated original name, evaluated under the SAME retained valuation. They need not be constants or smaller than x. The arbitrary Boolean matrix may contain repeated/correlated occurrences, actual H, inverse symbols and the original x in any position. The signed source-argument domain is explicit; no negative input is silently admitted. Zero and below-first-range inverse behavior stay literal.

This supplies only the no-wide dominant plain-Phi branch. Exhaustive row normalization/dominance dispatch, the wide case, the hyper-Phi dominant branch, complementary close cases and alternating first-order closure remain unpaid. No whole numbered source claim or generic projection oracle is introduced. The exact six target propositions were frozen before proof authorship; native preflight is pending.
