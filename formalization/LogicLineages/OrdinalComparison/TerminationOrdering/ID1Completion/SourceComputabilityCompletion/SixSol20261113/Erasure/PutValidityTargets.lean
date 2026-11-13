module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidity
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual original guarded decoder accepts a PUT constructor with empty extra
arguments whenever it accepts the original ordinary node. No head signature,
child acceptance or validity of the target is supplied. -/
def ActualRawPutValidity : Prop :=
  ∀ (H : Program 1) (M W : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (raw target typ head base label nil gamma c : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 ordinaryConstructor raw head base ⊓
      (programGraph nilConstructor nil Fin.elim0 ⊓
        (programGraph numberedConstructor target ![label,head,typ,base,numeral 0,nil] ⊓
          OriginalUniverseDecoderTransport.Accepted H M W false typ raw gamma c))).imp
      (OriginalUniverseDecoderTransport.Accepted H M W false typ target gamma c)))

/-- The literal original PUT resultCode, not a newly chosen numbered target,
is accepted at the same original parameter. Its source is genuinely ordinary. -/
def ActualPackedPutValidity : Prop :=
  ∀ (H G : Program 1) (M W : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter typ raw head base label : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter ⊓
      (graph2 InternalPairing.pairing s typ raw ⊓
        (graph2 ordinaryConstructor raw head base ⊓
          graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label))).imp
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)))

/-- The SAME actual final selected source validator accepts the literal PUT
result; no alternate tuple or canonical fixedness is assumed or concluded. -/
def ActualFinalPutValidity : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter typ raw head base label : OTerm alpha),
  let D := OriginalTransparentDecoderValidatorCollapse.selected p H G W
  Nonempty (Derivation body Delta
    ((graph2 (InternalOriginalUniformDescentSelection.validity D) (numeral 1) s parameter ⊓
      (graph2 InternalPairing.pairing s typ raw ⊓
        (graph2 ordinaryConstructor raw head base ⊓
          graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label))).imp
      (graph2 (InternalOriginalUniformDescentSelection.validity D) (numeral 1) t parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidity
