module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportConstructorProof OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderInternalAcceptanceBinaryProof
  (actualOriginalTypedInternalApplicationAcceptance actualOriginalTypedInternalNumberedAcceptance
    actualOriginalTypedInternalConsAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tupleSixRename {beta : Type} (a b c d e f : OTerm alpha) (j : alpha → beta) :
    (fun i : Fin 6 => (![a,b,c,d,e,f] i).relabel j) =
      ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i

theorem applicationIff (H : Program 1) (raw domain fn arg typ arrow gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (ht : Nonempty (Derivation body Delta (StepCons arrow domain typ))) :
    Nonempty (Derivation body Delta
      ((Accepted H false typ raw gamma).iff
        (Accepted H false arrow fn gamma ⊓ Accepted H false domain arg gamma))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,conjunctionRename]
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph3Rename] at hc'
  rw [stepConsRename] at ht'
  have hf := applicationPairs (raw.relabel j) payload (domain.relabel j) (fn.relabel j) (arg.relabel j) hc' hp
  exact closedApply (actualOriginalTypedInternalApplicationAcceptance body H beta
    (raw.relabel j) payload (domain.relabel j) (fn.relabel j) (arg.relabel j)
    (typ.relabel j) (arrow.relabel j) (gamma.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) ht'))

theorem numberedIff (H : Program 1)
    (raw label head recorded base extraTypes extras headData headResult baseTypes typ gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData headResult baseTypes))) :
    Nonempty (Derivation body Delta
      ((Accepted H false typ raw gamma).iff
        ((equal headData (numeral 0)).not ⊓
          (equal recorded typ ⊓
            (Accepted H true baseTypes base gamma ⊓ Accepted H true extraTypes extras gamma))))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,conjunctionRename,notRename,equalRename,numeral,zRelabel]
  have hc' := renameInto hc j Theta hj
  have hh' := renameInto hh j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [programRename,tupleSixRename] at hc'
  rw [graph1Rename] at hh'
  rw [stepArrowFieldsRename] at ht'
  have hf := numberedPairs (raw.relabel j) payload (label.relabel j) (head.relabel j)
    (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) hc' hp
  exact closedApply (actualOriginalTypedInternalNumberedAcceptance body H beta
    (raw.relabel j) payload (label.relabel j) (head.relabel j) (recorded.relabel j)
    (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (headData.relabel j)
    (headResult.relabel j) (baseTypes.relabel j) (typ.relabel j) (gamma.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) (andIntro hh' ht')))

theorem consIff (H : Program 1)
    (raw domain head tail types requestedDomain tailTypes gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields types requestedDomain tailTypes))) :
    Nonempty (Derivation body Delta
      ((Accepted H true types raw gamma).iff
        ((equal types (numeral 0)).not ⊓
          (equal requestedDomain domain ⊓
            (Accepted H false domain head gamma ⊓ Accepted H true tailTypes tail gamma))))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,conjunctionRename,notRename,equalRename,numeral,zRelabel]
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph3Rename] at hc'
  rw [stepArrowFieldsRename] at ht'
  have hf := consPairs (raw.relabel j) payload (domain.relabel j) (head.relabel j) (tail.relabel j) hc' hp
  exact closedApply (actualOriginalTypedInternalConsAcceptance body H beta
    (raw.relabel j) payload (domain.relabel j) (head.relabel j) (tail.relabel j)
    (types.relabel j) (requestedDomain.relabel j) (tailTypes.relabel j) (gamma.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) ht'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
