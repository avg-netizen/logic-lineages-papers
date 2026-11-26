module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumInterchangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open Continuation20261115.BoundsRecombination (maximum)
open MaximumBaseProof (forward backward)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem interchange (a b c bc ac left right : OTerm alpha)
    (hbc : Nonempty (Derivation body Delta (graph2 maximum bc b c)))
    (hac : Nonempty (Derivation body Delta (graph2 maximum ac a c)))
    (hl : Nonempty (Derivation body Delta (graph2 maximum left a bc)))
    (hr : Nonempty (Derivation body Delta (graph2 maximum right b ac))) :
    Nonempty (Derivation body Delta (eqn left right)) := by
  have hl1 := forward a bc left left hl (InternalCoprimeMultipleBoundedProof.selfLtSucc left)
  have hl2 := forward b c bc left hbc (andRight hl1)
  have hr1 := forward b ac right right hr (InternalCoprimeMultipleBoundedProof.selfLtSucc right)
  have hr2 := forward a c ac right hac (andRight hr1)
  exact MaximumAlgebraProof.weakAntisymmetric left right
    (backward a bc left right hl (andLeft hr2)
      (backward b c bc right hbc (andLeft hr1) (andRight hr2)))
    (backward b ac right left hr (andLeft hl2)
      (backward a c ac left hac (andLeft hl1) (andRight hl2)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumInterchangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumInterchangeProof
