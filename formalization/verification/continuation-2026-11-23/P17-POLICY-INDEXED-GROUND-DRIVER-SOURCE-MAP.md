# Indexed ground comparison driver, conditional on literal indexed source compilation

The two parsing-policy-dependent operations in #1428 are the calls to
`PolicySourceInterface.compile p d a` and `compile p d b`; after they
return, the original body uses only the normalized scalar codes, the
positive-coordinate test, relation tag, query builder, and closed-block
answer routine. This packet supplies the same decision body, but takes
one indexed source compiler and one common policy-program index for both
actual term inputs. It preserves the original left-to-right sequencing:
first completed refusal returns false immediately, and second completed
refusal returns false only when the first compilation succeeded. If an
executed source call diverges, the entire result is undefined rather than
false. A valid indexed source compiler is a hypothesis.

The pointwise comparison is against the exact function body of
`GroundComparisonAssemblyProof.lean` with the real original source
compiler, not an arbitrary decider from an existence result. The
effectivity extends the same primitive/recursive computation of the
policy-independent body through two partial binds on source results.
No indexed source compiler or full numbered comparison theorem is claimed.

The final conditional packet composes that driver with the original
ground canonical reduction and the admitted #1418 closed-block query,
then invokes #1431 on the natural encoding of the common partial
program. It quantifies one primitive-recursive transformer before the
supplied selector code, per relation and fixed control, and returns the
exact successful Boolean answer for all admitted typed ground contexts.
The last specialization uses the original #1423 query compiler and its
calibration; the remaining premise is a jointly partial-recursive
source compiler exact against the original literal source operation.
The separate functional-hardness/control-law clauses are unchanged.
