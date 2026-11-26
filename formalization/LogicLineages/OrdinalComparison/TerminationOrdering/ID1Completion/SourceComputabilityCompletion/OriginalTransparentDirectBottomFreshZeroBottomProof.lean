module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalPackedProof
open OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof

theorem eraseBottom (t out typ d cutoff : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
 (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw out d cutoff t))) :
 Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode out typ)) := by
 apply programCases bottomConstructor (Fin.cons typ Fin.elim0) _
 intro beta rho Theta raw hrho hr
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hr
 rw [graph1Rename]
 have hb' := renameInto hb rho Theta hrho
 have he' := renameInto he rho Theta hrho
 rw [graph1Rename] at hb'
 rw [graph3Rename] at he'
 have hp := OriginalVariableErasureCertificateRawProof.bottomCodePair (t.relabel rho) raw (typ.relabel rho) hr hb'
 have hraw : Nonempty (Derivation body Theta (graph3 eraseRaw raw (d.relabel rho) (cutoff.relabel rho) raw)) :=
  bottomBackward .erase raw raw (d.relabel rho) (cutoff.relabel rho) (typ.relabel rho) hr
   (by simpa only [OriginalRawSyntaxTransportInternal.UnchangedLeafResult,equalEqn] using (show Nonempty (Derivation body Theta (InternalTagArithmeticSyntaxProof.eqn raw raw)) from ⟨InternalTagArithmeticSupportProof.refl raw⟩))
 have hs := erasePackedBackward (t.relabel rho) (t.relabel rho) (typ.relabel rho) raw raw (d.relabel rho) (cutoff.relabel rho) hp hraw hp
 have hsame := valueUnique erasePackedRaw (t.relabel rho) (out.relabel rho) ![d.relabel rho,cutoff.relabel rho,t.relabel rho] hs he'
 exact outputTransport BottomRepresentative.bottomCode (t.relabel rho) (out.relabel rho) (Fin.cons (typ.relabel rho) Fin.elim0) hsame hb'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroBottomProof
