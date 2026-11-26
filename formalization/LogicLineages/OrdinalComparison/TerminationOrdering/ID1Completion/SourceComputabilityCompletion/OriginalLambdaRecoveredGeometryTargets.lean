module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Recover actual target geometry and the literal extended runtime context from
same-leaf child elimination. No target constructor, canonicality, or transport
law is assumed. Fresh extension is queried internally; the recovered child
and certificate are retained, never replaced by independently accepted ones. -/
def ActualOriginalLambdaRecoveredGeometry : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (leaf : Program 4) (s t cert parameter oldChild childS childT childCert childParam
     d e arrow context gamma : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e oldChild arrow)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
 Nonempty (Derivation body Delta (OriginalHereditaryLambda.ChildRecovered leaf
   s t cert parameter childS childT childCert childParam)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (extended : OTerm beta),
  (∀ p ∈ Delta, p.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta
   (equal (childS.relabel j) (oldChild.relabel j) ⊓
    (OriginalLambdaConstructor.Fields (t.relabel j) (d.relabel j) (e.relabel j)
       (childT.relabel j) (arrow.relabel j) ⊓
     (graph3 OriginalLambdaConstructor.constructor (t.relabel j) (d.relabel j)
        (e.relabel j) (childT.relabel j) ⊓
      (graph2 InternalListCodec.consCode extended (d.relabel j) (gamma.relabel j) ⊓
       (graph2 InternalPairing.pairing (childParam.relabel j) (context.relabel j) extended ⊓
        graph4 leaf InternalOriginalStepGuard.one (childS.relabel j) (childT.relabel j)
          (childCert.relabel j) (childParam.relabel j))))))) →
  Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryTargets
