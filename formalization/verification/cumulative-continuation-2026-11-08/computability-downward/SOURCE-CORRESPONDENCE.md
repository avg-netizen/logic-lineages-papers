# Original computability downward-closure reduction

The source obligation is the type-recursive computability downward-closure
argument in `06-godel-t-termination-ordering/paper.tex`, within `lem:id1`.
The target remains the original context-uniform internal accessibility theorem.

## Exact formulas and derivations

`computable` substitutes the original `JointGammaComputability.formula` at the
unchanged numeric context and an arbitrary arithmetic term. `edge` is the
original existential positive-certificate graph. `domain` contains only the
original typed function, typed argument and same-Gamma checker graphs.

The four frozen targets prove arrow introduction, full finite type induction
for downward closure from explicit local arithmetic rules, elimination of the
explicit certificate-transformer witnesses, and a calibrated source reduction.
Every internal conclusion inhabits the original `InternalCalculus.Derivation`.

The type-induction proof uses original even-tag accessibility closure at ground
type. At an arrow type, it transports the same-Gamma guard backwards, obtains
a computable application witness for the predecessor and an accepted witness
for the successor, applies the local arithmetic application-compatibility rule,
and invokes the codomain induction hypothesis. All hypotheses and free names
survive the two existential eliminations. The domain type's potentially negative
predicate occurrences remain in the original formula.

`CertifiedApplicationLift` is an explicit remaining hypothesis. Its inputs are
the original `[context, domain type, codomain type, argument, certificate]`.
Its premise includes the actual transformer's graph and its conclusion is the
original positive checker's accepting graph at that same transformed witness.
The reduction obtains this witness using checked internal Program totality.
It never obtains an internal proof from an external evaluation equality.

The uniform source theorem selects one calibrated source/computability pair
before all subtype-closed source windows. It discharges typed preservation,
guard transport and typed application totality for that same pair. It selects
an all-input calibrated original path transformer, but does not infer the
missing symbolic correctness theorem from that calibration.

## Acceptance and boundary

All four exact aliases passed the native checker and actual axiom audit.
The type-induction and arrow-introduction aliases use only `propext` and
`Quot.sound`; the two source/certificate reductions additionally use
`Classical.choice`. Frozen definitions and targets were not modified.

The internal certificate lift remains unproved. Consequently unconditional
arbitrary-type downward closure and the numbered `lem:id1` statement remain
pending. This component completes their type-induction consumer and isolates
the concrete arithmetic proof that must supply it.
