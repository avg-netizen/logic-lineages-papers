# From the actual finite stage to the whole ranked compiler

This is the continuation plan, not an accepted theorem. The frozen whole
endpoint remains `ContractTargets.FullRankedCancellation`. R004's concrete
finite stage must first prove its unchanged syntax, all-child intrinsic
decrease, exact value/domain semantics and encoded computability targets.

## Exact values throughout

Every descending child preserves its parent's actual integer `RowValue`.
The ordinary-class branch emits undoubled residual coefficients and integer
corrections. Its proof uses R001's doubled identity, the zero doubled leader
coefficient, and cancellation of two in the integers. There is no accumulated
scaling factor to remove at a final linear leaf. The counter-only collision
branch is already an exact undoubled identity.

## A finite work stack

Process one source row per packet; combine the final finite case lists for a
row family by a Cartesian product of guards and outcome lists. A work item is
an actual current Row, its accumulated original-name Boolean guard, and the
paid cutoff. Finished cases carry that guard and their literal Outcome.

One machine step pops the first work item, evaluates its complete finite
syntax-directed stage, appends finished branches to the case list, and pushes
all actual descending branches onto the work stack. It conjoins the parent's
accumulated guard with each new branch guard. The global paid cutoff is the
maximum of every visited branch payment. No guard is tested for consistency;
all branches, including inconsistent ones, have intrinsic decrease and valid
syntax.

Define an external proof-only tree size by well-founded recursion on the
intrinsic RowLess relation:

`size(row) = 1 + sum(size(child) for every actual descending stage branch)`.

This is a proof of termination, not a value supplied to the machine. The sum
of these sizes over the actual work stack decreases by exactly one per active
machine step. It therefore yields an existential finite stopping time without
introducing a new multiset order on stacks. The old histogram well-foundedness
core handles the local row relation; the machine termination measure is Nat.

## Effectivity

Specify a concrete numeric state using original Row data, encoded Boolean
guards and encoded finished outcomes. R004's ActualStageProgram computes the
exact list of encoded branches. Existing formula encode equations compute
guard conjunctions. The finite machine step and its fuel iteration can then
be shown computable directly on numeric states.

Search for the first fuel whose actual work stack is empty. Prove that the
Boolean stopping predicate is computable and that a fuel exists from the
tree-size argument. The already used `Computable.find` / least-stopping-fuel
pattern then gives a total computable output, without requiring the external
tree-size function to be computable or weakening termination to a premise.
Malformed source data must take an explicit immediate invalid branch.

## Semantics and domains

Track every work/finished item's source-name containment, source-degree
admission, unconditional maximum-linearity of accumulated guards, and exact
source-row value under its guard. For any valuation above the final paid
cutoff, every visited stage's Region follows from source-name containment and
the original maximum-variable premise. Thus every original and generated
domain is available, including in false branches.

At each machine step, R004 coverage replaces an active accumulated guard by
the disjunction of its finitely many child/finished guards. R004 exact value
preservation transfers the source row's meaning down every true child. At
the empty stack, the finished cases cover all original valuations and yield
their actual strict signs or exact equal-valued linear rows. Producting the
single-row outputs supplies the unchanged finite-family whole-source target.

L4 then combines this compiler with actual all-input prefix evaluation,
composed-word residues and its word-linear QE. The closed existential loop
decreases the number of original raw quantified names. Arbitrary free-parameter
or alternating word quantifier elimination remains outside this route.

Concrete candidates now authored:

- `RunnerTerminationProof`: actual histogram well-foundedness, proof-only
  row tree cost, exact one-node stack cost drop, all-input stopping and exact
  least stopping. It uses the actual stage theorem, with no new runtime field.
- `RunnerCodeProof`: numeric WorkData/CaseData/EncodedState execution,
  conjunction-code construction, literal child/finished collection, and
  finite-run calibration to `encodeState (Runner.run ...)`. No guard decoder
  or consistency test is present.

The remaining source correctness invariant is over the exact pending stack
and finished singleton cases. All rows/guards retain original names and
admission; accumulated guards are unconditionally linear in the maximum.
On every valuation in the state's paid original-name region, every guard and
row has its domain, every true work guard preserves the original row value,
every true finished case has the original row outcome, and at least one
pending/finished guard is true. `step` raises paid to the actual stage cutoff;
original-name support supplies the stage's region. Stage domains hold even
for false branches. A true parent guard is replaced by a true actual child
or finished guard using stage coverage, without testing consistency. An empty
work stack then leaves exactly the original one-row PackageCorrect result.

The numeric finite step composes actual encoded stage output with primitive
map/filter/append and conjunction codes. Numeric finite iteration is genuinely
Computable by fuel recursion. The proved all-input stopping then licenses
Computable minimization for the literal leastFuel. Family output is the exact
Cartesian product of single-row packages, with outcome lists concatenated
in original source order. All these are proof obligations until native exact
gates and actual transitive axiom checks pass.
