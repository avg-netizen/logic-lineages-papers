module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.NormalizationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SupportProof

theorem toClass (T : Program 2) (P : Program 3) (root probe parameter : OTerm alpha)
    (hself : Nonempty (Derivation body Delta (graph3 P (suc z) root root parameter)))
    (hr : Nonempty (Derivation body Delta (graph3 (OriginalTransparentMinimum.reflexiveClassTest T P) (suc z) root probe parameter))) :
    Nonempty (Derivation body Delta (graph3 P (suc z) root probe parameter)) := by
  apply casesOrder probe root
  · exact (zeroDirection T P root probe parameter
      (InternalEqualityTestProof.rejectForwardOrder probe root ⟨Derivation.hypothesis List.mem_cons_self⟩)).mp (withHyp hr _)
  · exact probeTransport P root root probe parameter
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (withHyp hself _)
  · exact (zeroDirection T P root probe parameter
      (InternalEqualityTestProof.rejectBackwardOrder probe root ⟨Derivation.hypothesis List.mem_cons_self⟩)).mp (withHyp hr _)

theorem toReflexive (T : Program 2) (P : Program 3) (root probe parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 T (suc z) root parameter)))
    (hp : Nonempty (Derivation body Delta (graph3 P (suc z) root probe parameter))) :
    Nonempty (Derivation body Delta (graph3 (OriginalTransparentMinimum.reflexiveClassTest T P) (suc z) root probe parameter)) := by
  apply casesOrder probe root
  · exact (zeroDirection T P root probe parameter
      (InternalEqualityTestProof.rejectForwardOrder probe root ⟨Derivation.hypothesis List.mem_cons_self⟩)).mpr (withHyp hp _)
  · exact equalReflexive T P root probe parameter ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ht _)
  · exact (zeroDirection T P root probe parameter
      (InternalEqualityTestProof.rejectBackwardOrder probe root ⟨Derivation.hypothesis List.mem_cons_self⟩)).mpr (withHyp hp _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.NormalizationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.NormalizationProof
