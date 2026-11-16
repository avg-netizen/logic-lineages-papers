module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.GuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)

theorem recover (n : Nat) (arity : Fin n → Nat) (head context symbols types : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph2 (window n arity) (numeral 1) head context)))
    (hs : Nonempty (Derivation body Delta (graph1 contextSymbols symbols context)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context))) :
    Nonempty (Derivation body Delta
      (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
       graph3 (Continuation20261114.OriginalHeadWindow.window n arity) (numeral 1) head symbols types)) := by
  let xs : Fin 2 → OTerm alpha := ![head,context]
  let C : Program 2 := .composition (Continuation20261115.OriginalDecodedContextValidity.contextGuard n)
    (fun _ : Fin 1 => .projection 1)
  let V : Program 2 := .composition (Continuation20261115.OriginalHeadDecoderValidity.check n)
    (fun _ : Fin 1 => .projection 0)
  have outer := conjunctionRecover C (InternalAcceptance.conjunction V (rawWindow n arity)) xs hw
  have inner := conjunctionRecover V (rawWindow n arity) xs (andRight outer)
  have hv := unaryRecover (Continuation20261115.OriginalHeadDecoderValidity.check n) (.projection 0)
    (numeral 1) head xs (andLeft inner) (projectionValue 0 xs)
  have hsyms := unaryValue contextSymbols (.projection 1) symbols context xs hs (projectionValue 1 xs)
  have htypes := unaryValue OriginalUniverseDomainCoverage.contextTypes (.projection 1) types context xs ht (projectionValue 1 xs)
  have hraw := ternaryRecover (Continuation20261114.OriginalHeadWindow.window n arity)
    (.projection 0) (.composition contextSymbols (fun _ : Fin 1 => .projection 1))
    (.composition OriginalUniverseDomainCoverage.contextTypes (fun _ : Fin 1 => .projection 1))
    (numeral 1) head symbols types xs (andRight inner) (projectionValue 0 xs) hsyms htypes
  exact andIntro hv hraw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.GuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.GuardProof
