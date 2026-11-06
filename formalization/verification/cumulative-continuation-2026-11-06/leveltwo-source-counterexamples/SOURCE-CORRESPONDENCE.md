# Canonical level-two source counterexamples

Source: `08-multivariate-collapse-comparison/paper.tex`, Theorem
`thm:leveltwo`, lines 795–824, particularly the source-to-existential reduction
in lines 815–821. This component closes that reduction, not the decision step.

The frozen target starts with actual `OriginalTerm` values in a ground free
context and `InternalLevelBound 2` for both terms. It includes all internal
subterm and binder types. There is no premise asserting assignment success,
vector compilation success, polynomial heads, or existence of a solver.
The actual canonical default policy is used; arbitrary policy semantics is
not a claim of an arbitrary policy's effective computability.

The existing actual-source compilation and polynomial-head classification
supply the compiler outputs and head bounds. The accepted scalar adapter
normalizes the actual scalar syntax and translates it to the existing
polynomial graph compiler. Neither classification nor graph correctness is
reproved. Original occurrences use `SourceTypedPorts.variableIndex`; shared
and repeated names do not become independent witnesses.

The actual closed positive coordinates are normalized and compared. Mode 0
is weak comparison, mode 1 is WW-strict comparison (strict at coordinate zero,
weak at every positive coordinate), and all other modes are equality with
the source's zero padding. The pair matrix fails the actual positive flag
or the correct scalar relation. It quantifies all original and fresh names.
Original variables retain the positive-natural domain; graph nodes range
over all naturals. `groundPositiveTupleComplete` supplies the reverse
valuation direction, rather than assuming an arbitrary ordinal-component
valuation already factors through raw indices.

The literal numeric `SourceCode.compile` consumes original term codes,
invokes the actual default source vector compiler, and emits the pair package.
Its primitive recursiveness is proved on all numeric inputs. Correctness and
successful output are certified on the stated actual internal-level-two
class only. The package retains a finite degree computed from each pair;
there is no uniform bound across inputs.

## Decision and undecidability boundary

`Pair.Closed` is a semantic existential proposition, not an implemented truth
procedure. The native theorem gives exact equivalence to a source
counterexample and a primitive-recursive translation. It does not give a
primitive-recursive, computable, or merely terminating decision procedure
for the emitted sentence. Nor does it claim undecidability of this restricted
image. A translation alone establishes neither outcome.

The paper's remaining route invokes `thm:existential` (lines 708–744), whose
proof depends on the guard and row transformations. Those obligations are
not imported as assumptions or bypassed here. This work is independent of
recovery and proof work on those suppliers, and does not resolve them or II5
transitivity. The full `thm:leveltwo` register entry remains pending.
