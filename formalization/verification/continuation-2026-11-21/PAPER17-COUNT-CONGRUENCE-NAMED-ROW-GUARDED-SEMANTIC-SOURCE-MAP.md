# Count-congruence named row: corrected guarded semantic target only

Printed source: controls.tex:172–183 and arithmetic.tex:231–240, as in
PAPER17-COUNT-CONGRUENCE-NAMED-ROW-SOURCE-MAP.md. The single generated
coordinate slot has exactly the original raw value x, not an independently
sampled value. The intended quantification over slot assignments is
agreement implies the whole evaluation equivalence.

The previously frozen ActualNamedRow is unchanged; so are its original
candidate proofs, code, statements, manifests, and receipts. Its written
last clause parsed as a quantifier over an iff whose left side is an
implication: for every nu, (nu 1 = x implies p.eval nu) iff the original
divisibility test. The exact archived native diagnostic at semantic proof
line 168 introduces nu but cannot introduce its agreement hypothesis.
This is a false frozen statement, not a tactic-only failure.

Concrete mathematical counterexample to the frozen parse: choose the
factorial selected control at B=0, lambda=omega and mu=0 (proper), rank
zero, m=2, and signed coefficients c=1, u=v=0. Set rho constantly to x,
where x is the original exact coded tail, so all outer requirements hold.
For any proposed actual count witness i, the right-hand test is 2 divides
1, false. Take nu constantly x+1: the left implication has false
antecedent and is true regardless of the emitted row. Thus no witness can
satisfy the frozen quantified iff. This is a read-only mathematical
counterexample to the frozen Lean target, not a counterexample to the
printed source and not a new machine-checked theorem.

ActualNamedRowGuarded adds only explicit parentheses around the inner
evaluation iff. It keeps every other binder, guard, domain and actual
read conclusion, and reuses the exact original row/tail definitions and
all signed semantics. It does not claim prior semantic or aggregate
acceptance, does not modify the earlier CodeExact result, and adds no
whole #704, all-strip, or numbered scope. Fresh target-only preflight
and independent review are required before proof work.
