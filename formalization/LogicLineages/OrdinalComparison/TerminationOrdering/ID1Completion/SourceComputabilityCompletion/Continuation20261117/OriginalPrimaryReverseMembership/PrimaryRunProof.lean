module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimaryRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn z sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem recover (T P : Program 2) (E : Program 3)
 (seed parameter pool out count : OTerm alpha)
 (had : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 P pool seed parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) out seed parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.countOfPool P) count seed parameter))) :
 Nonempty (Derivation body Delta (graph4 (PrimaryIteration.run E) out count pool seed parameter)) := by
 have hr := InternalAcceptanceBranchProof.successorBranchElim T (InternalAcceptance.constantZero 2)
   (.composition (PrimaryIteration.run E) ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1])
   out z ![seed,parameter] had hl
 apply compositionRecover (PrimaryIteration.run E)
   ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1]
   out ![seed,parameter] ![count,pool,seed,parameter] hr
 intro i
 exact Fin.cases hc (Fin.cases hp (Fin.cases (projectionValue 0 ![seed,parameter])
   (Fin.cases (projectionValue 1 ![seed,parameter]) (fun k => Fin.elim0 k)))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimaryRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimaryRunProof
