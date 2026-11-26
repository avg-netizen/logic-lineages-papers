module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AbsentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.OptionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
theorem symmetry : Targets.InternalSymmetry := by
  intro body alpha Delta source target ha
  apply OptionProof.bothCases source target _ ha
  intro beta j Theta left right hj hl hr hp
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  exact (OriginalArgumentPermutation.InternalProof.internalSome body beta Theta (target.relabel j) (source.relabel j)
    right left (numeral 1) hr hl).mpr (CountClosureProof.permutationSymmetric left right hp)

theorem transitivity : Targets.InternalTransitivity := by
  intro body alpha Delta source middle target hab hbc
  apply OptionProof.bothCases source middle _ hab
  intro beta j Theta left middleList hj hl hm hp
  have hbcj := renameInto hbc j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hbcj
  apply OptionProof.bothCases (middle.relabel j) (target.relabel j) _ hbcj
  intro gamma k Xi otherMiddle right hk hm2 hr hp2
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hlj := renameInto hl k Xi hk
  have hmj := renameInto hm k Xi hk
  have hpj := renameInto hp k Xi hk
  simp only [graph2Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj hmj hpj
  obtain ⟨he⟩ := valueUnique ArgumentEntriesRecursor.extract (suc otherMiddle) (suc (middleList.relabel k))
    ![(middle.relabel j).relabel k,numeral 0] hm2 hmj
  have hp2' := headTransport ArgumentCountComparison.permutation (numeral 1) otherMiddle (middleList.relabel k)
    (Fin.cons right Fin.elim0) ⟨cancelSuc he⟩ hp2
  exact (OriginalArgumentPermutation.InternalProof.internalSome body gamma Xi ((source.relabel j).relabel k)
    ((target.relabel j).relabel k) (left.relabel k) right (numeral 1) hlj hr).mpr
    (CountClosureProof.permutationTransitive (left.relabel k) (middleList.relabel k) right hpj hp2')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.Proof
