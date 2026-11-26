# Paper 17 guarded count-congruence row

Paper 17 `sections/controls.tex` lines 172–183 give the original proper
entry count and its exact affordability tail. `sections/arithmetic.tex`
lines 231–240 require the same raw input residue modulo \(2m\) for every
occurrence. This packet treats one original signed count and coordinate row.

The new `FullGuardedCountCongruenceNamedRow` combines the unchanged
`CodeExact` result from 746, the separately checked `ShapeAndSupport` proof,
and the unchanged `ActualNamedRowGuarded` result from 749. The proof of
shape and support depends on the original short-gap recognition and an
induction on the literal disjunction fold. All its atoms use the single
generated positive name 1, tied to the original raw coordinate. The
guarded semantics applies the whole evaluation equivalence when the
valuation at name 1 agrees with that coordinate.

The previous unguarded comparator and failed aggregate remain preserved.
The new proof closure does not import either of their statement checks or
the failed semantic proof. Mixed field rows, unprepared strips and their
coverage, and the printed scope qualifications for #704 remain open here.
