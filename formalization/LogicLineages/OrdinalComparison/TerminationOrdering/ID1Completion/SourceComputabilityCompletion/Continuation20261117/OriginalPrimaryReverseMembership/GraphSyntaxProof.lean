module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114

theorem graphTwoSubst {alpha beta : Type} (P : Program 2) (out x y : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (graph2 P out x y).subst (fun a => emb (ts a)) = graph2 P (out.subst ts) (x.subst ts) (y.subst ts) := by
 simp only [graph2,programSubst,consTermSubst,emptySubst]
theorem graphThreeSubst {alpha beta : Type} (P : Program 3) (out x y z : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (graph3 P out x y z).subst (fun a => emb (ts a)) = graph3 P (out.subst ts) (x.subst ts) (y.subst ts) (z.subst ts) := by
 simp only [graph3,programSubst,consTermSubst,emptySubst]

theorem graphFourSubst {alpha beta : Type} (P : Program 4) (out a b c d : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (graph4 P out a b c d).subst (fun a => emb (ts a)) = graph4 P (out.subst ts) (a.subst ts) (b.subst ts) (c.subst ts) (d.subst ts) := by
 simp only [graph4,programSubst,consTermSubst,emptySubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
