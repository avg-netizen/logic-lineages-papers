module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.TaggedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atPair (n : Nat) (raw encoded tag payload : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) raw)))
    (he : Nonempty (Derivation body Delta (graph1 Continuation20261114.OriginalHeadEncodingBridge.encodeHead encoded raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload))) :
    Nonempty (Derivation body Delta (graph1 (convert n) raw encoded)) := by
  have ha := (OriginalHeadDecoderValidity.Proof.internalAcceptedBranches n body alpha Delta raw tag payload hp).mp hv
  apply CasesProof.allowedElim n tag payload (graph1 (convert n) raw encoded) ha
  intro i
  let B := CasesProof.branch n i tag payload
  have hb : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact TaggedProof.atBranch n i raw tag payload encoded (withHyp hp B) hb (withHyp he B)

theorem inverse (n : Nat) (raw encoded : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) raw)))
    (he : Nonempty (Derivation body Delta (graph1 Continuation20261114.OriginalHeadEncodingBridge.encodeHead encoded raw))) :
    Nonempty (Derivation body Delta (graph1 (convert n) raw encoded)) := by
  apply OriginalDecodedRank.SupportProof.pairCases raw (graph1 (convert n) raw encoded)
  intro beta j Theta tag payload hj hp
  simp only [graph1Rename]
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph1Rename] at hej
  exact atPair n (raw.relabel j) (encoded.relabel j) tag payload hvj hej hp

theorem internalInverse : Targets.InternalInverse := by
  intro body alpha Delta n raw encoded hv he
  exact inverse n raw encoded hv he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Proof
