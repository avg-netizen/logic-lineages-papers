module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalPackedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof hiding andIntro andLeft andRight
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalPackedProof
open OriginalTwoDeletionInternalDefinitions OriginalTwoDeletionInternalSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open InternalAcceptanceSupportProof (programCases)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem packedAt6 (supply : OriginalTwoDeletionInternalTargets.RawCommutation) (packed a b i j upper lower left right tau raw uc lc xc yc : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields erasePackedRaw packed a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tau packed)))
    (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw packed)))
    (h2 : Nonempty (Derivation body Delta (graph3 eraseRaw uc b (suc j) raw)))
    (h3 : Nonempty (Derivation body Delta (graph3 eraseRaw lc a i raw)))
    (h4 : Nonempty (Derivation body Delta (graph3 eraseRaw xc a i uc)))
    (h5 : Nonempty (Derivation body Delta (graph3 eraseRaw yc b j lc)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  have hp := reconstructPair packed tau raw h0 h1
  have hu := erasePackedForward packed upper tau raw uc b (suc j) hp h2 (andLeft (andRight hf))
  have hx := erasePackedForward upper left tau uc xc a i hu h4 (andLeft (andRight (andRight hf)))
  have hl := erasePackedForward packed lower tau raw lc a i hp h3 (andLeft (andRight (andRight (andRight hf))))
  have hy := erasePackedForward lower right tau lc yc b j hl h5 (andRight (andRight (andRight (andRight hf))))
  obtain ⟨hraw⟩ := supply body alpha Delta raw a b i j uc lc xc yc
  obtain ⟨hargs⟩ := andIntro (andLeft hf) (andIntro h2 (andIntro h4 (andIntro h3 h5)))
  have he : Nonempty (Derivation body Delta (equal xc yc)) := ⟨Derivation.implicationElimination hraw hargs⟩
  have hx' : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing left tau yc)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta _ left
      (Fin.cons tau (Fin.cons xc Fin.elim0)) (Fin.cons tau (Fin.cons yc Fin.elim0)) _ hx
    intro t
    refine Fin.cases ?_ (fun v => ?_) t
    · change Nonempty (Derivation body Delta (equal tau tau))
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn tau tau)) from ⟨InternalTagArithmeticSupportProof.refl tau⟩)
    · refine Fin.cases ?_ (fun e => Fin.elim0 e) v
      exact he
  have h := valueUnique InternalPairing.pairing left right (Fin.cons tau (Fin.cons yc Fin.elim0)) hx' hy
  simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalPackedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalPackedProof
