# Remaining genuine series and mixed-word obligations

## Formal series rule and actual rational compatibility

The printed unbounded coefficient formula must not be reduced to finite polynomials without justification. A genuine next stack should define on actual `PowerSeries K` the coefficientwise odd selector with inverse Frobenius: Q.coeff n=sqrt(F.coeff(2*n+1)). Prove F=A²+X*B² and uniqueness in actual series, not just define C to have the desired output. This handles arbitrary infinite series coefficients in a perfect characteristic-two field.

Then prove compatibility with actual rational Cartier for functions regular at zero. Define the rational expansion independently as polynomial num times inverse polynomial denom, with the necessary denominator-at-zero unit condition proved where applicable. Show the rational square decomposition expands to the series square decomposition and use uniqueness to identify the odd part. Pay regularity of the two rational square-root digits; do not assume the desired expansion commutation. A still broader and coordinate-independent version uses actual Laurent series at z and all integer coefficients. That covers poles and allows the translated support estimates, but may import significantly more than the finite polynomial packet.

The old CartierLaurentProof/TranslatedRational modules are templates only: their real rational-to-Hahn embedding is substantial, not a ready thin import. Any old/new bridge must be genuinely compiled if used, and no cap increase is allowed. Current Basic definitions and accepted proofs remain unchanged. A separately reviewed series target should retain arbitrary series, actual rational expansion and precise regularity domain; no implicit finite-support restriction.

## Mixed Laurent contraction

For local h=X-z and local coefficients c_m of f, the exact L0 Laurent coefficient at n is sqrt(c_(2*n)+z*c_(2*n+1)); L1 is sqrt(c_(2*n+1)). Prove this through the actual translated rational embedding and X=h+z. It gives both no new poles and order contraction ceil(k/2). Unlike pure C, L0 can turn a double pole into a simple one, so profiles after the transient include contributions of initially higher poles.

Prove mixed properness independently via actual fraction degree or expansion at infinity: X*f adds at most a constant polynomial part to proper f and C kills that constant. Do not infer properness from finite local pole bounds alone (a nonzero polynomial has no finite poles).

Define actual low-bit-first execution of a list of selectors. Inductively retain properness, original finite pole support, and order bound ceil(k/2^length). Instantiate with actual denominator A_d, its proven multiplicity budget mu, and a=Nat.clog2 mu; no source support bound assumed as an oracle. Handle zero/d=0 and cancellation explicitly.

Only after this actual mixed transient and the independent full compatible-profile bijection/descent/output layer may the complete residue observer be promoted. The finite polynomial packet and Basic9 each remain supporting results.

## Pinned-library feasibility refinement

Pinned `PowerSeries.Expand` imports general substitution and multivariate expansion; avoid importing it merely for the coefficient-of-square rule if that again exhausts RSS. `PowerSeries.Trunc` instead imports polynomial coefficient/degree lemmas and PowerSeries.Basic. A source-exact route is to reduce each fixed coefficient of F² to the finite truncation through degree n, apply the already established polynomial characteristic-two square-coefficient rule, then prove the arbitrary-series square decomposition by coefficient extensionality. The quantified series itself is unrestricted; truncation is only a proof technique for each coefficient, not a finite-support assumption. This is an untested proof/import plan, not a native feasibility result.
