module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
structure PrimaryData (T P : Program 2) (E : Program 3) (body : Positive (Fin 1))
    {alpha : Type} (Delta : List (Formula alpha)) (seed parameter sourceOut candidate targetOut sourcePool targetPool : OTerm alpha) : Prop where
  sourceAdmitted : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter))
  targetAdmitted : Nonempty (Derivation body Delta (graph2 T (numeral 1) candidate parameter))
  sourcePoolGraph : Nonempty (Derivation body Delta (graph2 P sourcePool seed parameter))
  targetPoolGraph : Nonempty (Derivation body Delta (graph2 P targetPool candidate parameter))
  sourcePrimary : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) sourceOut seed parameter))
  targetPrimary : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) targetOut candidate parameter))
  member : Nonempty (Derivation body Delta (graph2 contains (numeral 1) sourceOut candidate))
  pools : Nonempty (Derivation body Delta (PrimaryMonotonicity.included targetPool sourcePool))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion
