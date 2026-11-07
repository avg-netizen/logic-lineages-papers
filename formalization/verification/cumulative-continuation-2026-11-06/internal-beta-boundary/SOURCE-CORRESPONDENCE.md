# Source correspondence

Discrete boundary literally uses OrdinaryArithmetic.lessFormula on arbitrary
ordinary terms. Its disjunction uses the original first-order connective.
The proof inducts on the original witness d of s+succ(d)=t: the zero case
gives succ(s)=t, and the successor case supplies the predecessor as witness
for succ(s)<t.

Wraparound retains the exact original beta parameters b and i, including the
literal modulus succ((succ i)*b). From its original quotient equation and
succ(r)=modulus it derives succ(a)=(succ(q))*modulus+0. The new strict-bound
witness is (succ i)*b, with remainder zero. All equations are derivations
in the unchanged calculus, not reflected semantic equalities.
