module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobExpansionCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalAgendaBindingProof OriginalHereditaryInternalAgendaTransportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem visitJob (H : Program 1) (M W : Program 2) (c B frame parent : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Frame H M W c B frame)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) parent))) :
 Nonempty (Derivation body Delta (Job H M W c B parent)) := by
 apply frameCases H M W c B frame _ hf
 intro beta j Theta actualParent payload counts hinc hfields
 rw [jobRename]
 have hp' := renameInto hp j Theta hinc
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp'
 apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases (andLeft hfields)
 · intro Xi inc hvisit
   have hgiven := weakenProof hp' inc
   have heq := valueUnique InternalUnpair.right actualParent (parent.relabel j) (Fin.cons (frame.relabel j) Fin.elim0)
    (pairRight (frame.relabel j) (numeral 0) actualParent hvisit)
    (pairRight (frame.relabel j) (numeral 0) (parent.relabel j) hgiven)
   exact jobTransport H M W (c.relabel j) (B.relabel j) actualParent (parent.relabel j)
    (by simpa only [equalEqn] using heq) (weakenProof (andRight hfields) inc)
 · intro Xi inc hreturn
   have hgiven := weakenProof hp' inc
   have heq := valueUnique InternalUnpair.left (numeral 0) (numeral 1) (Fin.cons (frame.relabel j) Fin.elim0)
    (pairLeft (frame.relabel j) (numeral 0) (parent.relabel j) hgiven)
    (pairLeft (frame.relabel j) (numeral 1) payload (andLeft hreturn))
   obtain ⟨heq⟩ := heq
   obtain ⟨hn⟩ := OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNe (body:=body) (Delta:=Xi) 0 1 (by decide)
   exact ⟨Derivation.explosion (Derivation.implicationElimination hn (by simpa only [equalEqn] using heq))⟩

theorem actualVisitPreservation : OriginalHereditaryInternalAgendaTargets.VisitPreservation := by
 intro body alpha Delta H M W c B work visit rest parent jobs tagged counts payload returnFrame returnRest next ha hw hv he ht hp hr hc happ
 have hframe := OriginalHereditaryInternalAgendaStructuralProof.head H M W c B work visit rest ha hw
 have hj := visitJob H M W c B visit parent hframe hv
 have htail := OriginalHereditaryInternalAgendaStructuralProof.tail H M W c B work visit rest ha hw
 have hret := OriginalHereditaryInternalAgendaStructuralProof.returnFrame H M W c B returnFrame parent payload counts hr hp hj
 have hrest := OriginalHereditaryInternalAgendaStructuralProof.cons H M W c B returnRest returnFrame rest hc hret htail
 have hrow := OriginalHereditaryInternalJobExpansionCasesProof.actualExpansion body alpha Delta H M W c B parent jobs hj he
 have htagged := OriginalHereditaryInternalJobRowMapProof.actualTagged body alpha Delta H M W c B jobs tagged hrow ht
 exact OriginalHereditaryInternalAgendaAppendProof.append H M W c B tagged returnRest next htagged hrest happ
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaVisitProof
