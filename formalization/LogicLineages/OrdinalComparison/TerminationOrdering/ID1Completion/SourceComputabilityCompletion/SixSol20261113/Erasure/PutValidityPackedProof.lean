module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityExposureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityPackedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalTransparentDecoderValidatorCollapsePackedProof (sourceFieldsElim sourceFieldsIntro)
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases selectorPair)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem withContext (H G : Program 1) (M W : Program 2)
    (s t parameter typ raw head base label c gamma : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hr : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)) := by
  apply PutValidityExposureProof.exposure s t typ raw head base label _ hp ho hr
  intro beta j Theta target nil hj hout hnil hnumbered
  simp only [graph2Rename,numeralRename]
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  have hc' := renameInto hc j Theta hj
  simp only [graph2Rename,numeralRename] at ha'
  rw [graph2Rename] at hp' ho' hc'
  have hf := sourceFieldsElim H G M W (s.relabel j) (parameter.relabel j)
    (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) hp' hc' ha'
  have accepted := PutValidityRawProof.raw H M W (raw.relabel j) target (typ.relabel j)
    (head.relabel j) (base.relabel j) (label.relabel j) nil (gamma.relabel j) (c.relabel j)
    ho' hnil hnumbered (andRight hf)
  exact sourceFieldsIntro H G M W (t.relabel j) (parameter.relabel j)
    (typ.relabel j) target (c.relabel j) (gamma.relabel j) hout hc' (andLeft hf) accepted

theorem packed (H G : Program 1) (M W : Program 2)
    (s t parameter typ raw head base label : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hr : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)) := by
  let qs : Fin 2 → Program 1 := ![leftOf (.projection 0),rightOf (.projection 0)]
  apply programsCases qs (Fin.cons parameter Fin.elim0)
  intro beta j Theta ys hj hs
  simp only [graph2Rename,numeralRename]
  let xs : Fin 1 → OTerm beta := ![parameter.relabel j]
  have hc := selectorPair (.projection 0) (parameter.relabel j) (ys 0) (ys 1) xs
    (projectionValue 0 xs) (hs 0) (hs 1)
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,numeralRename] at ha'
  rw [graph2Rename] at hp' ho' hr'
  exact withContext H G M W (s.relabel j) (t.relabel j) (parameter.relabel j)
    (typ.relabel j) (raw.relabel j) (head.relabel j) (base.relabel j) (label.relabel j)
    (ys 0) (ys 1) ha' hp' ho' hr' hc

theorem actualPackedPutValidity : PutValidity.ActualPackedPutValidity := by
  intro H G M W body alpha Delta s t parameter typ raw head base label
  let A := graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter ⊓
    (graph2 InternalPairing.pairing s typ raw ⊓
      (graph2 ordinaryConstructor raw head base ⊓
        graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := packed H G M W s t parameter typ raw head base label
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction out⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityPackedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityPackedProof
