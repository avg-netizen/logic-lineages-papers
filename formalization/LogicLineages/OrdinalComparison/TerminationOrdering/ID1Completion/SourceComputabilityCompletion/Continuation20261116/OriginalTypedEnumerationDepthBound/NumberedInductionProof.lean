module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open Continuation20261115 Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atDepth (n : Nat) (H : Program 1)
    (raw rootLabel head typ left types right pair size label depth leftTyp rightTyp gamma dl dr maximum : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw)))
    (hls : Nonempty (Derivation body Delta (InternalLessThan.strictLess left raw)))
    (hrs : Nonempty (Derivation body Delta (InternalLessThan.strictLess right raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlt : Nonempty (Derivation body Delta (accepted H true leftTyp left gamma)))
    (hrt : Nonempty (Derivation body Delta (accepted H true rightTyp right gamma)))
    (hld : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) dl left)))
    (hrd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) dr right)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum dl dr))) :
    Nonempty (Derivation body Delta (result false size depth)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (OriginalCodeBoundsConstructors.NumberedQueriesProof.queries n) ![rootLabel,left,right] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![rootLabel,left,right] i).relabel j) = ![rootLabel.relabel j,left.relabel j,right.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hlb,hlp,hrb,hrp,hlabel,hroot,hcanonical⟩ :=
    OriginalCodeBoundsConstructors.NumberedQueriesProof.recover n (rootLabel.relabel j) (left.relabel j) (right.relabel j) ys hq
  rw [SyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have ihj := renameInto ih j Theta hj
  have hlsj := renameInto hls j Theta hj
  have hrsj := renameInto hrs j Theta hj
  have hlgj := renameInto hlg j Theta hj
  have hrgj := renameInto hrg j Theta hj
  have hltj := renameInto hlt j Theta hj
  have hrtj := renameInto hrt j Theta hj
  have hldj := renameInto hld j Theta hj
  have hrdj := renameInto hrd j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at hgj hbj hpj hdj hlgj hrgj hldj hrdj hmj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hlsj hrsj
  rw [SyntaxProof.acceptedRename] at hltj hrtj
  have hil := ChildInductionProof.childResult n H true (raw.relabel j) (left.relabel j)
    (leftTyp.relabel j) (gamma.relabel j) (ys 0) (ys 1) (ys 2) (dl.relabel j)
    ihj hlsj hlgj hltj hlb hlp hldj
  have hir := ChildInductionProof.childResult n H true (raw.relabel j) (right.relabel j)
    (rightTyp.relabel j) (gamma.relabel j) (ys 3) (ys 4) (ys 5) (dr.relabel j)
    ihj hrsj hrgj hrtj hrb hrp hrdj
  exact NumberedMeasureProof.atValues n (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j)
    (pair.relabel j) (size.relabel j) (label.relabel j) (depth.relabel j)
    (ys 0) (ys 1) (ys 2) (dl.relabel j) (ys 3) (ys 4) (ys 5) (dr.relabel j)
    (maximum.relabel j) (ys 6) (ys 8) (ys 9) hcj hgj hbj hpj hdj hlb hlp hldj hrb hrp hrdj hmj hlabel hroot hcanonical hil hir
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedInductionProof
