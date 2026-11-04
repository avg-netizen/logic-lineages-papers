# Prospective ordinary arithmetic bridge

This is a future implementation map, not a theorem, proof acceptance record,
or whole-source status promotion. Acceptance of the contextual checker
candidates remains governed by their separate frozen targets and compiler
receipts. No arithmetic formula or internal ID1 derivation is accepted by this
note.

## Source scope and the relation to preserve

[Paper06](../../../../06-godel-t-termination-ordering/paper.tex), lines77–82,
fixes a finite ranked ground signature F and its strict total precedence.
Lines537–556 fix the finite subtype-closed type window S, quotient primary
equivalence by least numerical representatives, and name the induced one-step
relation H and its **positive** transitive closure R. The source calls both
relations arithmetic. The arithmetic simulation statement at lines625–658
uses one window S = Ty(s) for both endpoint translations.

The next representation theorem must preserve these existing relations:

* `NumberedQuotientPaths.QuotientEdge` in
  [NumberedQuotientPathsDefinitions.lean](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedQuotientPathsDefinitions.lean)
  is the actual quotient one-step relation.
* `NumberedQuotientPaths.PositivePath` in the same file is the actual positive
  closure. An empty path must not witness it, including when the endpoints
  coincide.
* `NumberedNumericQuotientEdgeProof.numericQuotientEdge` in
  [NumberedNumericQuotientEdgeProof.lean](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedNumericQuotientEdgeProof.lean)
  proves, for every actual parameter and endpoint pair,
  `QuotientEdge ... x y ↔ ∃ c, numericEdgeTest ... x y c = true`
  (with the displayed equivalence reversed in the declaration).
* `NumberedQuotientPathCertificatesProof.numericPositivePathCertificates` in
  [NumberedQuotientPathCertificatesProof.lean](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedQuotientPathCertificatesProof.lean)
  gives the corresponding exact equivalence between `PositivePath` and an
  existential certificate accepted by `positivePathTest`.

These semantic certificate equivalences already supply the final connection
from an arithmetic checker graph to H and R. There is no reason to introduce a
replacement reachability relation or to decide absence of a path.

## Available representation infrastructure

The checked finite primitive-recursive program syntax can be reused directly:

* `GorbowPRProgram.Program` and `GorbowPRProgram.evaluate` in
  [GorbowPRProgramDefinitions.lean](../../../LogicLineages/ComputabilityKnowledge/GorbowPRProgramDefinitions.lean)
  use zero, successor, projection, finite composition and primitive recursion.
* `GorbowPRProgram.Proof.allPrimitiveFunctions` in
  [GorbowPRProgramProof.lean](../../../LogicLineages/ComputabilityKnowledge/GorbowPRProgramProof.lean)
  proves that every `Primrec f` on a fixed finite natural tuple is computed by
  an actual finite `Program`. `unaryCorrespondence` provides its unary form.
  This is existence from a primitive-recursion proof, not an executable
  universal evaluator for arbitrary program input.
* Pinned Mathlib's `Mathlib/Logic/Godel/GodelBetaFunction.lean` supplies
  `Nat.beta`, `Nat.unbeta` and `Nat.beta_unbeta_coe`: every given finite list is
  represented by the beta sequence at its valid indices. It does **not**
  already provide a first-order formula for beta or a theorem representing
  every primitive-recursive function.
* Pinned Mathlib's `Mathlib/ModelTheory/Syntax.lean` and `Semantics.lean` supply
  `FirstOrder.Language`, `BoundedFormula`, `Formula`, `Realize`, relabeling,
  substitution, quantifiers and their semantic calibration lemmas. A pure
  arithmetic signature and the required graph compiler still need to be fixed.

No generic `Primrec`/`REPred` to ordinary arithmetic formula supplier was found
in the pinned `ModelTheory` or `Logic/Godel` sources. `Nat.Partrec.Code.evaln`,
`primrec_evaln` and `evaln_complete` in `Computability/PartrecCode.lean` are
external computation and finite-evaluation results. They do not remove the
formula-representation obligation.

Two existing project formula developments have different scopes:

* `Source.ActualHeadGraph.Arithmetic.Formula` in
  [ActualHeadGraphArithmeticDefinitions.lean](../../../LogicLineages/OrdinalComparison/ActualHeadGraphArithmeticDefinitions.lean)
  contains source `observation` atoms and permits only fixed-numeral scaling
  in its expression syntax. Its accepted purpose is source head-graph
  interpretation; it is not an ordinary arithmetic representation of these
  numerical checkers.
* `GorbowPRDefiningEquations.call` in
  [GorbowPRDefiningEquationsDefinitions.lean](../../../LogicLineages/ComputabilityKnowledge/GorbowPRDefiningEquationsDefinitions.lean)
  invokes the Gorbow language's `universalFunction` and introduces finite
  program defining equations into a theory. The associated internal numeral
  calculations do not by themselves eliminate that extra function symbol into
  ordinary arithmetic.

## Smallest substantive next supplier

Fix an ordinary first-order arithmetic language with exactly zero, successor,
addition and multiplication as function symbols, and equality. A dedicated
Mathlib `FirstOrder.Language` avoids importing semantic test leaves. Reusing
the arithmetic-only fragment of another existing syntax would require an
explicit fragment predicate and a proved elimination/independence result for
every extra symbol; it is not automatic.

Define a literal structural compiler on the already checked `Program` syntax.
With output variable0 and input variables1 through n, the prospective exact
target is:

```lean
-- Prospective names: these definitions/theorems do not yet exist.
graphFormula : {n : Nat} → GorbowPRProgram.Program n →
  arithmeticLanguage.Formula (Fin (n + 1))

∀ (n : Nat) (p : GorbowPRProgram.Program n)
  (v : List.Vector Nat n) (y : Nat),
  (graphFormula p).Realize (Fin.cases y v.get) ↔
    GorbowPRProgram.evaluate p v = y
```

The standard-natural-number structure for `arithmeticLanguage` is part of the
prospective definition. The compiler and this exact statement should be
separated and frozen before its proof is authored.

Zero, successor and projection give literal equalities. Composition introduces
finitely many intermediate values and conjoins the actual child graph
formulas. Primitive recursion introduces a coded finite sequence of successive
values, checks its initial value, checks every index below the recursion bound,
and checks its final value. `Nat.beta_unbeta_coe` supplies the finite-sequence
existence direction. The beta remainder condition itself can be expressed
using only multiplication, addition, equality and quantifiers: write
`a = q * ((i + 1) * b + 1) + r` together with `r < ((i + 1) * b + 1)`, and expand
the strict inequality in ordinary arithmetic. The two sequence-code components
may be separate existential variables, avoiding an unproved formula for the
current list codec or for numerical unpairing.

The language must not contain a constructor whose interpretation is
`numericEdgeTest`, `positivePathTest`, `Primrec`, `REPred`, program evaluation,
H, R, or an arbitrary semantic predicate. Calling such a constructor
“arithmetic” would only rename the missing theorem. No Diophantine, delta-zero
or sigma-one complexity strengthening is required by the source's plain
arithmetic claim.

## Exact specialization to H and R

Once the actual checker primitive-recursion gates and the graph compiler are
accepted, obtain finite programs for the numerical Boolean characteristic
functions, represent output1, and existentially quantify the **existing**
certificate input. The resulting prospective formula targets are literal
equivalences:

```text
HFormula.Realize(parameters, x, y)
  ↔ QuotientEdge n arity symbols S (tableAbove table) Gamma x y

RFormula.Realize(parameters, x, y)
  ↔ PositivePath
      (QuotientEdge n arity symbols S (tableAbove table) Gamma) x y
```

The current quotient certificate primitive-recursion targets fix n, arity and
Gamma, while varying the two window lists, the entire finite Boolean table,
and the natural endpoint/certificate data jointly. Their runtime parameters
can be exposed as their genuine numerical encodings in a single formula, with
malformed encodings rejected by the corresponding literal decoder. Exact
calibration on encodings of actual parameters is then a separate, explicit
part of the specialization. The accepted existential certificate equivalences
above finish both displayed targets without new semantic assumptions.

Do not infer a computable formula compiler uniform in Gamma from a theorem of
the form `∀ Gamma, ∃ formula`. Likewise, the source already fixes its finite F
and precedence; any additional requirement to vary n or arity must come from
the frozen whole-source interface, not from an automatic demand to strengthen
every historical supporting algorithm. The actual source translation, the
fixed source window S = Ty(s), and the semantic positive simulation still have
to be assembled in that interface before promoting `lem:simulation`.

## Separate internal ID1 obligations

Standard-natural-number graph correctness establishes arithmetic definability.
It does not produce a derivation in ID1. The source's `lem:id1` additionally
requires all of the following, with an actual formal language and derivation
system rather than semantic fields:

* Arithmetic typedness, the unchanged H and R, and the direct multiset
  replacement relation on the same finite window.
* The positive accessibility operators for terms and finite multisets,
  combined by disjoint numerical tags into an allowed single inductive
  definition, including the original typedness guards.
* Actual first-order formulas for the finite type-recursive computability
  clauses, with the exact permitted polarity and finite type disjunctions.
* Internal derivations of non-lambda and inverse-application facts, the lambda
  clause, multiset accessibility closure, the numbered-constructor
  lexicographic induction and structural computable substitution.

The later Bachmann–Howard inductive-norm extraction is a further mathematical
supplier. Neither external primitive recursiveness nor recursively enumerable
certificate acceptance establishes internal ID1 provability or that norm
bound. No such promotion is proposed here.
