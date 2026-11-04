# Source correspondence correction: plus and minus displacement

The first-round dependency note overstated the source cases paid by the
accepted `WindowTargets.ActualFiniteElimination`. That formal theorem is
correct and its accepted source/evidence bytes remain unchanged.

The accepted guard is
`Phi(anchor) <= Phi(x_i+e) <= c*Phi(anchor)`.
It produces `x_i+e=anchor+d`, `0<=d<=c`, and substitutes `anchor+d-e`.
This directly pays the source's close-summand casesII1/II2 (pp47--48).

CaseII5 (pp49--50) has the opposite orientation:
`Phi(x_j+k) <= Phi(hyperAnchor) <= c*Phi(x_j+k)`.
It produces `hyperAnchor=x_j+k+d`, hence needs the MINUS substitution
`x_j=hyperAnchor-d-k`. It is not a paid instance of the existing plus-only
compiler. A separate reverse-window semantic/support/literal-code/effectivity
contract and actual proof are required. The source's original domain and
comparison must remain in every branch, including all finite/default cases.

The accepted numerical coefficient-elimination bound supports both directions;
the missing work is this exact reverse-oriented substitution consumer.
The accepted HyperWindow component independently pays caseII6. LinearWindow
for casesII3/II4 is still a candidate. The full source decision/QE theorem
remains pending, including normalization, dominant cases and the induction.

This correction supersedes ONLY the first dependency note's claim that the
accepted plus window already covered caseII5. No numbered statement, frozen
comparison, accepted proof, source convention or compiler cap is changed.
