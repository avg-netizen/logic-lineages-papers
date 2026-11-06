# Finite original-source exposure across arbitrary rank gaps

Baseline: `28e1cd56d9020cd4c753538e51044ce15ac0b542`. All tracked baseline sources, manuscript, targets, checker/dependency files and register files are preserved.

## Exact finite construction

- Paper08 lines 283–300 and 604–608 repeatedly expand the higher source head until its outer rank matches the requested ordinary rank. Here the original rank is n+m+3 and the exposed rank is n+2, for arbitrary naturals n,m.
- `exposurePrefix n m c` contains m+1 retained unsigned heads, in descending evaluation order from rank n+m+3 through n+3. Each head has retained mass c+rank and index zero. It remains attached to the original argument.
- `exposureWord` appends the exact `lowerHead n c j`. For n=0 this is V with index j-ceil(c/2); for positive n it is a genuine admitted X of rank n+2. No rank-two X, inverse counter or extra subtraction from total output is introduced.
- `PrefixSyntax` proves the actual prefix and exposed word admitted, length m+1, no prefix E nodes, and the literal tag/index/rank bounds for every retained occurrence.

## Tail and original-source proof

The cutoff is exactly the recursively computed finite maximum of the accepted one-step `SourceRangeExpansion.expansionTail k c j` for k=n,…,n+m. Every retained unsigned source kernel is an iterate and dominates its actual input. Thus every recursive entry pays the same finite maximum and, in particular, the next original-source expansion threshold.

The source proof is induction on the finite rank gap, using only the accepted one-step original-source expansion. Its parent, inner and reached-child bridge thresholds remain explicitly paid by each step tail. The target keeps `sourceSignedValue` from the independently defined original schedule; no companion schedule is substituted by convention.

Both the original higher-head domain and the entire emitted word's dynamically reached domain are conclusions. No fresh independent interior input is introduced.

## Context and effectiveness

Paper08 lines 564–572 require structural offsets and domains at actual values. The contextual cutoff pays the expansion maximum at `wordValue A x` and the original complete A/head/S word domain. Exact prefix equality transfers all suffix domains and values, including negative shifts, with the same raw x and no suffix monotonicity requirement.

The literal finite prefix, exposed word, recursive maximum and complete contextual cutoff are uniformly primitive recursive in n, m, c, j, A and S. This is a computed finite maximum, not a guessed index envelope.

## Boundary

This supplies finite exposure for all positive ordinary-rank gaps. It does not yet apply the opposite-head comparator and strip it, prove the full recursive guard algorithm or global termination, handle terminal growth, or establish row cancellation or existential decision. No numbered source statement is promoted. Register remains 167 checked, 2 inherited, 20 pending / 189.
