module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerAtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SignatureQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalTypedDecoderStepSpecification (StepArrowFields)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open OriginalUniverseDecoderTransportSyntaxProof (acceptedRename)
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open OriginalTypedDecoderInternalScalarSyntaxProof (stepArrowFieldsRename)
open OriginalTypedDecoderTransportBinaryAcceptanceProof (tupleSixRename)

theorem ordinaryAtsource (n : Nat) (H : Program 1) (M W : Program 2)
    (left right f g base target typ gamma context sourceData sourceResult sourceTypes : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hperm : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hs : Nonempty (Derivation body Delta (graph1 H sourceData f)))
    (hsf : Nonempty (Derivation body Delta (StepArrowFields sourceData sourceResult sourceTypes)))
    (hw : Nonempty (Derivation body Delta (graph2 W (suc z) g context)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (OriginalTypedDecoderTransport.Accepted H false typ right gamma))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ right gamma context)) := by
  apply SignatureQueryProof.query H g _
  intro beta j Theta data result types hj hd hf
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  have hperm' := renameInto hperm j Theta hj
  have hs' := renameInto hs j Theta hj
  have hsf' := renameInto hsf j Theta hj
  have hw' := renameInto hw j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,acceptedRename,
    OriginalTypedDecoderTransportSyntaxProof.acceptedRename,stepArrowFieldsRename] at hlc' hrc' hbg' htg' hperm' hs' hsf' hw' ha' hp' ⊢
  exact CallerAtFieldsProof.ordinary n H M W (left.relabel j) (right.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (target.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) (sourceData.relabel j) (sourceResult.relabel j) (sourceTypes.relabel j) data result types
    hlc' hrc' hbg' htg' hperm' hs' hd hsf' hf hw' ha' hp'

theorem ordinaryComplete (n : Nat) (H : Program 1) (M W : Program 2)
    (left right f g base target typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hperm : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hw : Nonempty (Derivation body Delta (graph2 W (suc z) g context)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (OriginalTypedDecoderTransport.Accepted H false typ right gamma))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ right gamma context)) := by
  apply SignatureQueryProof.query H f _
  intro beta j Theta data result types hj hd hf
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  have hperm' := renameInto hperm j Theta hj
  have hw' := renameInto hw j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,acceptedRename,
    OriginalTypedDecoderTransportSyntaxProof.acceptedRename,stepArrowFieldsRename] at hlc' hrc' hbg' htg' hperm' hw' ha' hp' ⊢
  exact ordinaryAtsource n H M W (left.relabel j) (right.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (target.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) data result types
    hlc' hrc' hbg' htg' hperm' hd hf hw' ha' hp'

theorem numberedAtsource (n : Nat) (H : Program 1) (M W : Program 2)
    (left right label recorded extraTypes extras f g base target typ gamma context sourceData sourceResult sourceTypes : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,target,extraTypes,extras])))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hperm : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hs : Nonempty (Derivation body Delta (graph1 H sourceData f)))
    (hsf : Nonempty (Derivation body Delta (StepArrowFields sourceData sourceResult sourceTypes)))
    (hw : Nonempty (Derivation body Delta (graph2 W (suc z) g context)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (OriginalTypedDecoderTransport.Accepted H false typ right gamma))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ right gamma context)) := by
  apply SignatureQueryProof.query H g _
  intro beta j Theta data result types hj hd hf
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  have hperm' := renameInto hperm j Theta hj
  have hs' := renameInto hs j Theta hj
  have hsf' := renameInto hsf j Theta hj
  have hw' := renameInto hw j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,acceptedRename,
    OriginalTypedDecoderTransportSyntaxProof.acceptedRename,stepArrowFieldsRename,InternalControlGraphSupportProof.programRename,tupleSixRename] at hlc' hrc' hbg' htg' hperm' hs' hsf' hw' ha' hp' ⊢
  exact CallerAtFieldsProof.numbered n H M W (left.relabel j) (right.relabel j) (label.relabel j) (recorded.relabel j) (extraTypes.relabel j) (extras.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (target.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) (sourceData.relabel j) (sourceResult.relabel j) (sourceTypes.relabel j) data result types
    hlc' hrc' hbg' htg' hperm' hs' hd hsf' hf hw' ha' hp'

theorem numberedComplete (n : Nat) (H : Program 1) (M W : Program 2)
    (left right label recorded extraTypes extras f g base target typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,target,extraTypes,extras])))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hperm : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hw : Nonempty (Derivation body Delta (graph2 W (suc z) g context)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (OriginalTypedDecoderTransport.Accepted H false typ right gamma))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ right gamma context)) := by
  apply SignatureQueryProof.query H f _
  intro beta j Theta data result types hj hd hf
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  have hperm' := renameInto hperm j Theta hj
  have hw' := renameInto hw j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,acceptedRename,
    OriginalTypedDecoderTransportSyntaxProof.acceptedRename,stepArrowFieldsRename,InternalControlGraphSupportProof.programRename,tupleSixRename] at hlc' hrc' hbg' htg' hperm' hw' ha' hp' ⊢
  exact numberedAtsource n H M W (left.relabel j) (right.relabel j) (label.relabel j) (recorded.relabel j) (extraTypes.relabel j) (extras.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (target.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) data result types
    hlc' hrc' hbg' htg' hperm' hd hf hw' ha' hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerQueryProof
