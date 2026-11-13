module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionConsumer
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof (refl)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnCompletionSyntax (completionRename)
open UniformReturnShapeCompletion (weakenInto)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualUniformReturn : UniformReturnTargets.ActualUniformReturn := by
 intro R H M W body alpha Delta job role typ typed rawJob raw parameter gamma c children deletions counts payload frame produced
   hj ht hr hparameter ha harity hgamma hc hp hf hl
 apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.arityGraphCases raw children _ harity
 · intro Theta hi hn
   have hj' := weakenInto hj Theta hi
   have ht' := weakenInto ht Theta hi
   have hr' := weakenInto hr Theta hi
   have ha' := weakenInto ha Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hf' := weakenInto hf Theta hi
   have harity' := weakenInto harity Theta hi
   have hl' := weakenInto hl Theta hi
   have he := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) children (numeral 0)
     (Fin.cons raw Fin.elim0) harity' hn
   have hcnew := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing counts children deletions
     (numeral 0) deletions he ⟨refl deletions⟩ hc'
   obtain ⟨he⟩ := he
   have hlnew := outputTransport OriginalContextInsertion.length (add children deletions) (add (numeral 0) deletions)
     (Fin.cons produced Fin.elim0) ⟨InternalOriginalOrderProof.congAddRight deletions he⟩ hl'
   apply UniformReturnSupplierQueries.zeroCases deletions produced _ hlnew
   exact UniformReturnCompletionConsumer.completionConsumer R H M W
     job role typed typ rawJob raw parameter gamma c (numeral 0) deletions counts payload frame produced
     hj' ht' hr' ha' hcnew hp' hf'
 · intro Theta hi hn
   have hj' := weakenInto hj Theta hi
   have ht' := weakenInto ht Theta hi
   have hr' := weakenInto hr Theta hi
   have ha' := weakenInto ha Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hf' := weakenInto hf Theta hi
   have harity' := weakenInto harity Theta hi
   have hl' := weakenInto hl Theta hi
   have he := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) children (numeral 1)
     (Fin.cons raw Fin.elim0) harity' hn
   have hcnew := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing counts children deletions
     (numeral 1) deletions he ⟨refl deletions⟩ hc'
   obtain ⟨he⟩ := he
   have hlnew := outputTransport OriginalContextInsertion.length (add children deletions) (add (numeral 1) deletions)
     (Fin.cons produced Fin.elim0) ⟨InternalOriginalOrderProof.congAddRight deletions he⟩ hl'
   apply UniformReturnSupplierQueries.oneCases deletions produced _ hlnew
   exact UniformReturnCompletionConsumer.completionConsumer R H M W
     job role typed typ rawJob raw parameter gamma c (numeral 1) deletions counts payload frame produced
     hj' ht' hr' ha' hcnew hp' hf'
 · intro Theta hi hn
   have hj' := weakenInto hj Theta hi
   have ht' := weakenInto ht Theta hi
   have hr' := weakenInto hr Theta hi
   have ha' := weakenInto ha Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hf' := weakenInto hf Theta hi
   have harity' := weakenInto harity Theta hi
   have hl' := weakenInto hl Theta hi
   have he := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) children (numeral 2)
     (Fin.cons raw Fin.elim0) harity' hn
   have hcnew := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing counts children deletions
     (numeral 2) deletions he ⟨refl deletions⟩ hc'
   obtain ⟨he⟩ := he
   have hlnew := outputTransport OriginalContextInsertion.length (add children deletions) (add (numeral 2) deletions)
     (Fin.cons produced Fin.elim0) ⟨InternalOriginalOrderProof.congAddRight deletions he⟩ hl'
   apply UniformReturnSupplierQueries.twoCases deletions produced _ hlnew
   exact UniformReturnCompletionConsumer.completionConsumer R H M W
     job role typed typ rawJob raw parameter gamma c (numeral 2) deletions counts payload frame produced
     hj' ht' hr' ha' hcnew hp' hf'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnProof
