module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityRawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalTypedDecoderStepSpecification
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportLogicalProof OriginalTypedDecoderInternalScalarProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open OriginalTypedDecoderTransportBinaryAcceptanceProof (tupleSixRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rawAt (H : Program 1) (M W : Program 2)
    (raw target typ head base label nil gamma c headData result types : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hn : Nonempty (Derivation body Delta (programGraph nilConstructor nil Fin.elim0)))
    (hp : Nonempty (Derivation body Delta
      (programGraph numberedConstructor target ![label,head,typ,base,numeral 0,nil])))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ target gamma c)) := by
  have old := iffForward
    (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff H M W
      raw head base headData result types typ gamma c ho hh hf) ha
  have nilAccepted := iffBackward
    (OriginalUniverseDecoderTransportLeafAcceptanceProof.nilIff H M W nil (numeral 0) gamma c hn)
    (andIntro (equalReflexive (numeral 0)) (equalReflexive (numeral 0)))
  exact iffBackward
    (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff H M W
      target label head typ base (numeral 0) nil headData result types typ gamma c hp hh hf)
    (andIntro (andLeft old) (andIntro (andLeft (andRight old))
      (andIntro (andLeft (andRight (andRight old)))
        (andIntro (equalReflexive typ)
          (andIntro (andRight (andRight (andRight (andRight old)))) nilAccepted)))))

theorem raw (H : Program 1) (M W : Program 2)
    (raw target typ head base label nil gamma c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hn : Nonempty (Derivation body Delta (programGraph nilConstructor nil Fin.elim0)))
    (hp : Nonempty (Derivation body Delta
      (programGraph numberedConstructor target ![label,head,typ,base,numeral 0,nil])))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ target gamma c)) := by
  let qs : Fin 3 → Program 1 := ![H,OriginalTypedDecoder.headOf H,OriginalTypedDecoder.tailOf H]
  apply programsCases qs (Fin.cons head Fin.elim0)
  intro beta j Theta ys hj hs
  simp only [consTermRename,emptyRename] at hs
  simp only [acceptedRename]
  have ho' := renameInto ho j Theta hj
  have hn' := renameInto hn j Theta hj
  have hp' := renameInto hp j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ho'
  simp only [programRename,emptyRename] at hn'
  simp only [programRename,tupleSixRename,numeralRename] at hp'
  rw [acceptedRename] at ha'
  have hh : Nonempty (Derivation body Theta (graph1 H (ys 0) (head.relabel j))) := hs 0
  have hf := arrowFields H (ys 0) (ys 1) (ys 2)
    (Fin.cons (head.relabel j) Fin.elim0 : Fin 1 → OTerm beta) (hs 0) (hs 1) (hs 2)
  exact rawAt H M W (raw.relabel j) (target.relabel j) (typ.relabel j)
    (head.relabel j) (base.relabel j) (label.relabel j) (nil.relabel j)
    (gamma.relabel j) (c.relabel j) (ys 0) (ys 1) (ys 2) ho' hn' hp' hh hf ha'

theorem actualRawPutValidity : PutValidity.ActualRawPutValidity := by
  intro H M W body alpha Delta raw target typ head base label nil gamma c
  let A := graph2 ordinaryConstructor raw head base ⊓
    (programGraph nilConstructor nil Fin.elim0 ⊓
      (programGraph numberedConstructor target ![label,head,typ,base,numeral 0,nil] ⊓
        Accepted H M W false typ raw gamma c))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := PutValidityRawProof.raw H M W raw target typ head base label nil gamma c
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction out⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityRawProof
