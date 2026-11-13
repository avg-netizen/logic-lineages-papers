module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.GraphSharedValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Runtime SixSol20261113.Erasure
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem iffAt (P Q : Program 2) (packed parameter value out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 P value packed parameter)))
    (hq : Nonempty (Derivation body Delta (graph2 Q value packed parameter))) :
    Nonempty (Derivation body Delta ((graph2 P out packed parameter).iff (graph2 Q out packed parameter))) := by
  let A := graph2 P out packed parameter
  let C := graph2 Q out packed parameter
  have hh : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp' := InternalApplicationValidityStackAppendInductionCoreProof.withHyp hp A
  have hq' := InternalApplicationValidityStackAppendInductionCoreProof.withHyp hq A
  have he := valueUnique P value out (Fin.cons packed (Fin.cons parameter Fin.elim0)) hp' hh
  obtain ⟨forward⟩ := outputTransport Q value out (Fin.cons packed (Fin.cons parameter Fin.elim0)) he hq'
  have hh2 : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp2 := InternalApplicationValidityStackAppendInductionCoreProof.withHyp hp C
  have hq2 := InternalApplicationValidityStackAppendInductionCoreProof.withHyp hq C
  have he2 := valueUnique Q value out (Fin.cons packed (Fin.cons parameter Fin.elim0)) hq2 hh2
  obtain ⟨backward⟩ := outputTransport P value out (Fin.cons packed (Fin.cons parameter Fin.elim0)) he2 hp2
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.GraphSharedValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.GraphSharedValueProof
