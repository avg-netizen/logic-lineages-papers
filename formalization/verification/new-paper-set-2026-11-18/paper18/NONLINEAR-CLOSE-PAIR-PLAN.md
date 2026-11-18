# Next genuine multivariate elimination dependency: close nonlinear pair

## Published proof inspected

Visually read Snyatkov2008 printed pp42–51 from the exact cited PDF (text extraction has broken glyph mapping), in particular Theorem1's negated-existential induction and Theorem2's inverse-endpoint refinement. Primary source: https://eprints.tversu.ru/id/eprint/494/1/19950136_2008_2_snyatkov.pdf .

The proof is not simply repeated independent interval cuts. Page42 normalizes to integer sums of shifted variables, f(v+k), and f(F(v+e)+h). Page43 resolves divisibility through modular periodicity, handles purely linear bound variables, orders remaining variables and partitions by the maximum nonlinear occurrence. Pages44–46 split dominant-versus-remainder: a dominant term gives parameter-dependent inverse cuts and a fixed-width neighborhood, or a satisfiable interior branch. Pages47–50 handle a second comparable occurrence with six nonlinear/linear type pairings; two comparable f occurrences force one argument into a uniformly bounded distance of the other. The mixed f(F(...))/f(...) cases additionally use presence/absence of the corresponding higher occurrence to choose bounded-variable versus finite-neighborhood reduction. Page51 uses actual f/F inverse expressions to remove the fresh threshold witness. The arbitrary-alternation step is the preceding negated-existential induction, not a free consequence of an existential solver.

## Proposed next supporting bundle

Implement the finite-neighborhood substitution step for the comparable f-argument cases (pp47–50), operating on an ARBITRARY existing expanded Matrix, not only on a simple interval atom. This is a direct branch of multivariate nonlinear conjunction elimination, leaving all other coupled inequalities/congruences and negations intact.

Fix eliminated raw name x, nonnegative literal shift k and positive literal multiplier C. Let v be any existing expanded Term with x absent; it may contain repeated remaining variables and nested Phi/H/inverses/fixed arithmetic. The actual close-pair guard is

    Phi(v) <= Phi(x+k) AND Phi(x+k) < C*Phi(v).

All values are actual natural arithmetic under the same valuation. Prove a concrete computable width, e.g. delta=C+1, from actual fixed-control shift growth and positivity: every guard witness has v <= x+k < v+delta. No supplied width/inverse/domain oracle. C=0 is an explicit false branch; C=1 may have no witnesses and must remain exact.

For j in range(delta), create candidate term (v+j)-k with guard k<=v+j to prevent natural-truncation artifacts. Substitute this candidate for EVERY occurrence of x in the ENTIRE original guarded Matrix, preserving raw names/correlation; keep the original close-pair guard inside each disjunct. The output is an explicit finite disjunction with no quantifier. Require exact equivalence for every shared valuation between its evaluation and exists n, closeGuard AND M under Function.update ν x n. M is unrestricted in the existing expanded Matrix grammar, including nonlinear terms, arbitrary Boolean structure and fixed congruences. v is fresh for x; M need not be. No bound-renaming is needed because Matrix is quantifier-free; later first-order lifting must separately pay capture/shadowing.

Required internal lemmas: actual uniform shift domination; full Term/Matrix substitution semantics under Function.update; free-name containment; exact finite candidate completeness and soundness with low-end guard; output has no x; raw encoded substitution/finite branch compiler is total computable with literal-code calibration (prefer PR if the concrete recursion permits it). Compiler input has arbitrary codes and must not take semantic proof arguments. A typed syntax compiler alone is not the effectivity endpoint.

## What this does and does not pay

This handles the close-pair branch when the eliminated occurrence is Phi(x+k). Remaining parameter argument v may be H(y+e)+h, so this is not separate-input solving and does cover genuine mixed multivariate cases after the printed orientation split. It does not itself justify that a given row reaches the close-pair branch, handle the linear runner-up contradiction, or eliminate a variable occurring only under H. Those require the maximum-occurrence case partition and hyperlevel growth suppliers.

Still unpaid for complete m:thm:snyatkov: effective full source-to-normal-form flattening with fresh witnesses; modular normalization; signed-row collection/scaling and original/generated domain guards; dominant-term and six-case branch coverage; linear Presburger elimination; the well-founded bound-variable-count reduction including newly exposed nonlinear forms; and arbitrary negation/alternation reconstruction. Common/balanced translations alone do not supply any of these. No numbered promotion from this supporting rule.

Conceptual review requested before concrete definitions/targets/freeze or proof. No native execution.
