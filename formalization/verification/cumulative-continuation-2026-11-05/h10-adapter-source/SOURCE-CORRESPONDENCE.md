# Total H10 adapter source correspondence

The input language is `DiophantineCompletion.encodedPolynomialSolvable`:
standard outer natural encoding of a finite list, the unchanged sign/magnitude
and variable-length integer-polynomial parser, original index well-formedness,
and a zero-allowing natural root of the interpreted polynomial.

The output language is the distinct functional-hardness
`encodedPolynomialSolvable`: a standard code for a finite simultaneous system
with fixed integer-polynomial coefficients and shared unknowns in N[X].

The concrete adapter first checks the original parser and every original index.
It then applies the existing explicit substitution P(Y-1), the existing positive
straight-line circuit compiler, and the new primitive-recursive literal linear
system compiler. All failure branches return a fixed well-formed system 1=0.

The original validation is essential. An invalid original variable can coincide
with a compiler-generated wire, so later circuit well-formedness alone cannot
validate an original polynomial input. Zero coefficients are also checked.

The five supporting comparators distinguish malformed-input safety, exact
arbitrary-valid-parse calibration, primitive recursiveness, the unsatisfiable
fallback, and natural-root/positive-circuit transport. The unchanged original
CodedH10ToLinearSystems contract is only a target supplier until full circuit
satisfiability equivalence is independently proved and assembled. No
undecidability assumption or effective extraction from a Diophantine proof is
part of this adapter.
