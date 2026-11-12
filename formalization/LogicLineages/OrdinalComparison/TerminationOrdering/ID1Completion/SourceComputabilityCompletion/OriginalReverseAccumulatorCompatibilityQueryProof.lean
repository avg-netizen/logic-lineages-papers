module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions (accumulated)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consCases (raw head tail acc result : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated result raw acc)))
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (nextAcc : OTerm beta),
   (∀ p ∈ Delta, p.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode nextAcc (head.relabel rho) (acc.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 accumulated (result.relabel rho) (tail.relabel rho) nextAcc)) →
   Nonempty (Derivation body Theta (psi.relabel rho))) : Nonempty (Derivation body Delta psi) := by
 apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons acc Fin.elim0)) psi
 intro beta rho Theta nextAcc hrho ha
 simp only [consTermRename,emptyRename] at ha
 have hc' := renameInto hc rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 rw [graph2Rename] at hc' hv'
 apply programCases accumulated (Fin.cons (tail.relabel rho) (Fin.cons nextAcc Fin.elim0)) _
 intro gamma eta Xi actual heta hh
 simp only [consTermRename,emptyRename] at hh
 have hc'' := renameInto hc' eta Xi heta
 have hv'' := renameInto hv' eta Xi heta
 have ha' := renameInto ha eta Xi heta
 rw [graph2Rename] at hc'' hv'' ha'
 have hfull := OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof.consValue
   ((raw.relabel rho).relabel eta) ((head.relabel rho).relabel eta) ((tail.relabel rho).relabel eta)
   ((acc.relabel rho).relabel eta) (nextAcc.relabel eta) actual hc'' ha' hh
 have he := valueUnique accumulated actual ((result.relabel rho).relabel eta)
   (Fin.cons ((raw.relabel rho).relabel eta) (Fin.cons ((acc.relabel rho).relabel eta) Fin.elim0)) hfull hv''
 have ht := outputTransport accumulated actual ((result.relabel rho).relabel eta)
   (Fin.cons ((tail.relabel rho).relabel eta) (Fin.cons (nextAcc.relabel eta) Fin.elim0)) he hh
 have hnext := next gamma (eta ∘ rho) Xi (nextAcc.relabel eta)
   (fun p hp => by simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using heta _ (hrho p hp))
   (by simpa only [Term.relabel_relabel] using ha') (by simpa only [Term.relabel_relabel] using ht)
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hnext

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityQueryProof
