module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (argumentsAcceptedRename)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
theorem actualCases : SpineCasesTargets.ActualCases := by
 intro H M W body alpha Delta types raw gamma c psi ha nilCase consCase
 apply OriginalTypedDecoderTransportTagSupportProof.rawTagCases raw psi
 · intro beta j Theta i payload hj htag hpair
   have ha' := renameInto ha j Theta hj
   rw [argumentsAcceptedRename] at ha'
   by_cases h6 : i.val = 6
   · rw [h6] at hpair
     exact nilCase beta j Theta hj
       (SpineCasesNilProof.atNil H M W (types.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) payload ha' hpair)
   · by_cases h7 : i.val = 7
     · rw [h7] at htag
       apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases (raw.relabel j) (psi.relabel j) htag
       intro beta' k Xi domain head tail hk hc
       have ha'' := renameInto ha' k Xi hk
       rw [argumentsAcceptedRename] at ha''
       apply SpineCasesConsProof.atCons H M W ((types.relabel j).relabel k) ((raw.relabel j).relabel k)
         ((gamma.relabel j).relabel k) ((c.relabel j).relabel k) domain head tail _ ha'' hc
       intro beta'' l Omega requested tailTypes hl ht hhead htail hbound
       have hc' := renameInto hc l Omega hl
       rw [graph3Rename] at hc'
       have hin : ∀ f ∈ Delta, f.relabel (l ∘ k ∘ j) ∈ Omega := by
         intro f hf
         simpa only [formulaRelabelComposition,Function.comp_assoc] using hl _ (hk _ (hj f hf))
       have result := consCase beta'' (l ∘ k ∘ j) Omega (domain.relabel l) (head.relabel l) (tail.relabel l)
         requested tailTypes hin
         (by simpa only [Term.relabel_relabel,Function.comp_assoc] using hc')
         (by simpa only [Term.relabel_relabel,Function.comp_assoc] using ht)
         (by simpa only [Term.relabel_relabel,Function.comp_assoc] using hhead)
         (by simpa only [Term.relabel_relabel,Function.comp_assoc] using htail)
         (by simpa only [Term.relabel_relabel,Function.comp_assoc] using hbound)
       simpa only [formulaRelabelComposition,Function.comp_assoc] using result
     · exact OriginalUniverseDecoderTransportRejectedProof.argumentsOther H M W i.val h6 h7
         (raw.relabel j) payload (types.relabel j) (gamma.relabel j) (c.relabel j) _ hpair ha'
 · intro beta j Theta tag payload hj hpair hu
   have ha' := renameInto ha j Theta hj
   rw [argumentsAcceptedRename] at ha'
   exact OriginalUniverseDecoderTransportRejectedProof.unknown H M W true
     (raw.relabel j) tag payload (types.relabel j) (gamma.relabel j) (c.relabel j) _ hpair hu ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesProof
