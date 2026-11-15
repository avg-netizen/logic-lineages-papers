module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.TaggedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat)
attribute [local irreducible] programGraph

theorem atPairs (f g ef eg ft fp gt gp : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g)))
    (hef : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)))
    (he : Nonempty (Derivation body Delta (eqn ef eg)))
    (hpf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f ft fp)))
    (hpg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing g gt gp)))
    : Nonempty (Derivation body Delta (eqn f g)) := by
  have hfa := (OriginalHeadDecoderValidity.Proof.internalAcceptedBranches n body alpha Delta f ft fp hpf).mp hf
  have hga := (OriginalHeadDecoderValidity.Proof.internalAcceptedBranches n body alpha Delta g gt gp hpg).mp hg
  apply CasesProof.allowedElim n ft fp (eqn f g) hfa
  intro i
  let B1 := CasesProof.branch i ft fp
  apply CasesProof.allowedElim n gt gp (eqn f g) (withHyp hga B1)
  intro j
  let B2 := CasesProof.branch j gt gp
  have hb1 : Nonempty (Derivation body (B1 :: Delta) B1) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb2 : Nonempty (Derivation body (B2 :: B1 :: Delta) B2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact TaggedProof.atBranches i j f g ft fp gt gp ef eg
    (withHyp (withHyp hpf B1) B2) (withHyp (withHyp hpg B1) B2)
    (withHyp hb1 B2) hb2 (withHyp (withHyp hef B1) B2) (withHyp (withHyp heg B1) B2)
    (withHyp (withHyp he B1) B2)

theorem atFirst (f g ef eg ft fp : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g)))
    (hef : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)))
    (he : Nonempty (Derivation body Delta (eqn ef eg)))
    (hpf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f ft fp)))
    : Nonempty (Derivation body Delta (eqn f g)) := by
  apply OriginalDecodedRank.SupportProof.pairCases g (eqn f g)
  intro beta j Theta gt gp hj hp
  simp only [eqnRelabel]
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  have hegj := InternalGraphCompositionFunctionalityProof.renameInto heg j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hej
  have hpfj := InternalGraphCompositionFunctionalityProof.renameInto hpf j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hpfj
  exact atPairs n (f.relabel j) (g.relabel j) (ef.relabel j) (eg.relabel j) (ft.relabel j) (fp.relabel j) gt gp hfj hgj hefj hegj hej hpfj hp

theorem forward (f g ef eg : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g)))
    (hef : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)))
    (he : Nonempty (Derivation body Delta (eqn ef eg)))
    : Nonempty (Derivation body Delta (eqn f g)) := by
  apply OriginalDecodedRank.SupportProof.pairCases f (eqn f g)
  intro beta j Theta ft fp hj hp
  simp only [eqnRelabel]
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  have hegj := InternalGraphCompositionFunctionalityProof.renameInto heg j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hej
  exact atFirst n (f.relabel j) (g.relabel j) (ef.relabel j) (eg.relabel j) ft fp hfj hgj hefj hegj hej hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CoreProof
