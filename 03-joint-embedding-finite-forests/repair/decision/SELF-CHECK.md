# Exact repair self-check

Author-side full reading only; a separate mathematical review is still due.

The original target is unchanged. Its preliminary Carter-main route was
replaced by the explicitly saved ROUTE-AMENDMENT. The proof has NO Carter
theorem input. Three independent standard inputs are listed exactly; all
new transfer/effectivity lemmas have proofs rather than correctness fields.

Rechecked2016 Example7's exact ranked, ORDERED dive/couple recursion. Labels
in {a:0,U:2,J:2} enforce arities, so the ideal decomposition never produces
malformed expressions. Actual Section5.1 constructs the STRE from the
automaton; normalization and Theorem23 supply the finite regular ideals.
The source explicitly allows DIFFERENT fillings at repeated placeholders,
so no copy-equality/nonregular-language requirement is being imported.

One-way homeomorphic embedding implies graph containment. Conversely,
literal binary leaf pruning gives a smaller TERM without AC flattening.
That is the sufficient heredity bridge; no general graph-to-term converse
is needed or asserted. Directedness and covering of graph images then hold
literally. The finite ideal-cover lemma takes a common GRAPH host for its
finite witnesses and never demands a common host for their chosen parses.

The profile automaton records SETS of all induced graph types up to the
input bound, with empty included. Equation(2) computes those sets exactly.
Acceptance is a semantic forbidden-graph test, independent of tree shape.
The short P4 characterization proof also checks: in the mixed-component
case v,a,c,b has exactly the three required path edges and no chords;
the spanning-tree leaf makes H connected. Thus general cograph completeness
does not depend on Carter's transfer assertion either.

AC saturation stores ALL possible original automaton states. CFG terminals
are child STATE-SUBSET types, so each repeated occurrence can choose its
own state. Actual multiplicities, arbitrary binary associations and all
permutations are retained. A Parikh vector belongs to the start-q grammar
iff a representation with root state q really exists, in both directions.
Exact output subsets require negative predicates as well as positive ones;
the resulting transitions remain Presburger. Canonical arity and alternating
root tags are checked in the state space.

Boolean inclusion uses deterministic product state COUNT projections.
Productivity is a finite least fixed point with Presburger satisfiability
at each step. Its witnesses really produce finite trees, with repeated
copies allowed, and every finite tree is covered by the height induction.
There is no unbounded search stopping claim or assumed implementation.

Both empty graph cases are explicit: forbidden empty gives empty K;
empty nonempty-parse language gives empty-only K. Each has vacuous/trivial
JEP. Otherwise the finite ideal cover is nonempty. The independent-through-
four example is handled correctly even though its binary parse language
fails JEP. No old width, age, graph-bridge or certificate proof is changed.

Potential review focus: exact availability of individual regular automata
from2016 tree products; no nonlinear simultaneous-placeholder filling;
the two directions of CFG multiset interpretation; and Boolean inclusion
over UNORDERED canonical cotrees rather than the non-Boolean ordered/mixed
Presburger models. No full algorithm code/Lean certification/novelty claim.
