module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.EqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat)
attribute [local irreducible] programGraph

def relation (f g : OTerm alpha) : Formula alpha :=
  ((graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g).imp (eqn f g)) ⊓
  ((eqn f g).imp (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g))
theorem relationRename {beta : Type} (f g : OTerm alpha) (j : alpha → beta) :
    (relation f g).relabel j = relation (f.relabel j) (g.relabel j) := by
  simp only [relation,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,eqnRelabel,
    graph2Rename,GuardedSourceSyntaxProof.numeralRename]

theorem atOutputs (f g ef eg : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g)))
    (hef : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)))
    : Nonempty (Derivation body Delta (relation f g)) := by
  apply andIntro
  · let A := graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g
    have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := OriginalDecodedOrdinaryRecurrence.EqualityProof.recover
      OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg
      (withHyp hef A) (withHyp heg A) ha
    obtain ⟨h⟩ := (OriginalValidHeadEncodingInjectivity.Proof.validEncoding n body alpha (A :: Delta)
      f g ef eg (withHyp hf A) (withHyp hg A) (withHyp hef A) (withHyp heg A)).mp he
    exact ⟨Derivation.implicationIntroduction h⟩
  · let A := eqn f g
    have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := (OriginalValidHeadEncodingInjectivity.Proof.validEncoding n body alpha (A :: Delta)
      f g ef eg (withHyp hf A) (withHyp hg A) (withHyp hef A) (withHyp heg A)).mpr ha
    obtain ⟨h⟩ := OriginalDecodedOrdinaryRecurrence.EqualityProof.introduce
      OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg
      (withHyp hef A) (withHyp heg A) he
    exact ⟨Derivation.implicationIntroduction h⟩

theorem atFirst (f g ef : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g)))
    (hef : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)))
    : Nonempty (Derivation body Delta (relation f g)) := by
  apply programCases OriginalHeadEncodingBridge.encodeHead (Fin.cons g Fin.elim0) _
  intro beta j Theta eg hj hx
  simp only [consTermRename,emptyRename] at hx
  rw [relationRename]
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hefj
  exact atOutputs n (f.relabel j) (g.relabel j) (ef.relabel j) eg hfj hgj hefj hx

theorem accepted (f g : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g)))
    : Nonempty (Derivation body Delta (relation f g)) := by
  apply programCases OriginalHeadEncodingBridge.encodeHead (Fin.cons f Fin.elim0) _
  intro beta j Theta ef hj hx
  simp only [consTermRename,emptyRename] at hx
  rw [relationRename]
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
  exact atFirst n (f.relabel j) (g.relabel j) ef hfj hgj hx
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.EqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.EqualityProof
