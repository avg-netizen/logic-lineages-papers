module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimePaddingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CompletedAgreementProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalTagArithmeticSupportProof (trans symm)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualCompletedAgreement : FramedCompletionTargets.ActualCompletedAgreement := by
 intro R body alpha Delta first second input left right hf hle hs hre
 let xs : Fin 2 → OTerm alpha := Fin.cons (add first second) (Fin.cons input Fin.elim0)
 apply programCases (OriginalHereditaryRuntimeIterationDefinitions.run R) xs _
 intro beta j Theta shared hinc hshared
 rw [eqnRelabel]
 simp only [consTermRename,emptyRename,addRelabel] at hshared
 have hf' := renameInto hf j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hle' := renameInto hle j Theta hinc
 have hre' := renameInto hre j Theta hinc
 simp only [graph2Rename] at hf' hs'
 simp only [OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename] at hle' hre'
 have ha := OriginalHereditaryRuntimePaddingProof.actualPadding R body beta Theta
   (first.relabel j) (second.relabel j) (input.relabel j) (left.relabel j) shared hf' hle' hshared
 have hcomm := InternalAdditionCancellationProof.commutativity (body := body) (Gamma := Theta)
   (first.relabel j) (second.relabel j)
 have hswapped := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) shared
   (add (first.relabel j) (second.relabel j)) (add (second.relabel j) (first.relabel j))
   (Fin.cons (input.relabel j) Fin.elim0) ⟨hcomm⟩ hshared
 have hb := OriginalHereditaryRuntimePaddingProof.actualPadding R body beta Theta
   (second.relabel j) (first.relabel j) (input.relabel j) (right.relabel j) shared hs' hre' hswapped
 obtain ⟨ha⟩ := ha
 obtain ⟨hb⟩ := hb
 exact ⟨trans (symm ha) hb⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CompletedAgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CompletedAgreementProof
