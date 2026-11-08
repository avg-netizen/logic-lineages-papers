module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuard
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All wrapper nodes read [canonical source,canonical target,certificate].
The shared type is the OUTER TAG OF THE SOURCE ENDPOINT, not the certificate's
raw source, the target endpoint, or a separately selected semantic witness. -/
def sourceType : Program 3 := leftOf (.projection 0)

/-- The same selected binary typed Program is called on each endpoint at the
source endpoint's actual outer tag. No correctness field or new decoder is
stored in this finite original Program AST. -/
def typedAt (typedProgram : Program 2) (endpoint : Fin 3) : Program 3 :=
  .composition typedProgram ![.projection endpoint,sourceType]

/-- Exact-one conjunction retains the literal ORIGINAL quotient-edge checker.
Its target representative still decodes packed terms, without a global target
universe filter. Both selected canonical-typed calls are additional guards;
their external redundancy is a separate theorem requiring subtype closure. -/
def checker (data : InternalQuotientEdgeChecker.Data) (typedProgram : Program 2) : Program 3 :=
  InternalAcceptance.conjunction (InternalQuotientEdgeChecker.checker data)
    (InternalAcceptance.conjunction (typedAt typedProgram 0) (typedAt typedProgram 1))

def typed {α : Type} (typedProgram : Program 2) (value typ : OTerm α) : Formula α :=
  graph2 typedProgram InternalOriginalStepGuard.one value typ

def accepted {α : Type} (data : InternalQuotientEdgeChecker.Data) (typedProgram : Program 2)
    (x y certificate : OTerm α) : Formula α :=
  graph3 (checker data typedProgram) InternalOriginalStepGuard.one x y certificate

/-- An ACTUAL original arithmetic graph, not an external numeric equality or
an assumption that the selected typed Program already has a tag theorem. -/
def sourceTypeGraph {α : Type} (typ x : OTerm α) : Formula α :=
  graph1 InternalUnpair.left typ x

/-- Original core acceptance and BOTH selected typed predicates are retained.
The same symbolic type term occurs in both calls, without target typing as a
premise or a semantic truth-to-derivability principle. -/
def requirements {α : Type} (data : InternalQuotientEdgeChecker.Data) (typedProgram : Program 2)
    (x y certificate typ : OTerm α) : Formula α :=
  InternalQuotientEdgeChecker.accepted data x y certificate ⊓
    (typed typedProgram x typ ⊓ typed typedProgram y typ)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuard
