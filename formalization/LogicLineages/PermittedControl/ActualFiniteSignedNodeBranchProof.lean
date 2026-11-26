module
public import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchTargets
import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchSupportProof
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxSkeletonProof
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxRankProof
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsProof
import LogicLineages.PermittedControl.ActualReadChargeIterationProgressProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteSignedNodeBranch
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualRankedNormalizationSyntax (normalizedTerms extend exactNormalizedTermSkeleton
  exactOriginalSupportRankExtension)
open ActualFullLabelPairGuards (Answer)
open ActualFiniteFullValueGuards (Matches pairs ReadyFamily PaidFamily exactFiniteFullValueGuards)
open ActualMixedRowLeadingSum (rowParts rowCutoffCode exactEffectiveCutoff)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (normalizeReads)
open ActualReadChargeIteration (ReadState RankBound ActiveAt NodeGuards stateValue
  NonzeroTerminal ZeroEdge exactReadProgress)

private theorem interpretNode (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (θ : Nat → Nat) (r top z : Nat) (source : ReadState) (raw : List WeightedOperand)
    (a : List Answer)
    (strict : StrictMono θ) (topValue : θ top = z)
    (literal : source.reads.map Prod.fst = raw)
    (live : liftedReads f θ source.reads) (range : RankBound r top source)
    (active : StaticActive top raw) (guards : StaticGuards B θ raw)
    (matched : Matches f θ (pairs (nodeLabels raw)) a) :
    NodeResult f B θ r top z source raw a := by
  have frames (xs : List Read) (normal : normalizeReads f θ source.reads = some xs) :
      xs.map Prod.fst = normalizedTerms raw :=
    (exactNormalizedTermSkeleton.1 f θ source.reads xs normal).trans (congrArg normalizedTerms literal)
  have staticActive (xs : List Read) (normal : normalizeReads f θ source.reads = some xs) :
      ActiveAt top xs := by
    simpa only [StaticActive,ActiveAt,frames xs normal] using active
  have staticGuards (xs : List Read) (normal : normalizeReads f θ source.reads = some xs)
      (_active : ActiveAt top xs) : NodeGuards B θ xs := by
    simpa only [StaticGuards,NodeGuards,frames xs normal] using guards
  have actual := exactReadProgress f B hf θ strict r top source live range staticGuards
  rcases actual with final | zero
  · obtain ⟨xs,normalized,terminal⟩ := final
    have on := staticActive xs normalized
    rcases terminal with ⟨no,_⟩ | ⟨_,signReport⟩
    · exact False.elim (no on)
    · obtain ⟨anns,C,chosen,nonzero,eq,error,sign⟩ := signReport
      have relation := chosenCoefficient f B hf θ top raw a xs (frames xs normalized)
        guards matched anns C chosen
      have staticNonzero : nodeCoefficient raw a ≠ 0 := relation.symm ▸ nonzero
      have report : NonzeroTerminal f θ top source xs :=
        ⟨anns,C,chosen,nonzero,eq,error,sign⟩
      refine Or.inr ⟨staticNonzero,⟨xs,normalized,report⟩,?_⟩
      intro paid
      have current : rowCutoffCode source.constant ((xs.map Prod.fst).map encodeWeighted) ≤ θ top := by
        simpa only [frames xs normalized,topValue] using paid
      rw [exactEffectiveCutoff.2 source.constant (xs.map Prod.fst)] at current
      have actualSign := sign current
      simpa only [relation] using actualSign
  · obtain ⟨out,edge⟩ := zero
    obtain ⟨xs,anns,C,moved,ledger,anchor,q,normalized,_,_,chosen,witness⟩ := edge.actual
    have relation := chosenCoefficient f B hf θ top raw a xs (frames xs normalized)
      guards matched anns C chosen
    have canceled : (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) anns).1 = 0 := witness.2.2.1
    exact Or.inl ⟨relation.trans canceled,out,edge⟩

theorem exactFiniteSignedNodeBranch : ExactFiniteSignedNodeBranch := by
  intro f B hf ρ r top constant raw lower scope active ready a member
  have assembled := (exactFiniteFullValueGuards f B hf ρ top (nodeLabels raw) ready).1 a member
  refine ⟨assembled.1,assembled.2.1,?_⟩
  intro ν fit z above paid θ staticReady rs original rawLive guard
  obtain ⟨strict,topValue,same⟩ := exactOriginalSupportRankExtension ρ top z lower above
  have range := supported r top raw rs original scope
  have actuallyLive : liftedReads f θ rs :=
    (readTransport f θ (Function.update ρ top z) top same rs (fun rd h => (range rd h).2)).mpr rawLive
  have rawMatch := (assembled.2.2 ν fit z paid).mp guard
  have actualMatch := (matchedTransport f θ (Function.update ρ top z) top same (nodeLabels raw)
    (fun l hl => (ready.1 l hl).1) a).mpr rawMatch
  exact interpretNode f B hf θ r top z ⟨constant,rs⟩ raw a strict topValue original
    actuallyLive range active staticReady actualMatch

end LogicLineages.PermittedControl.ActualFiniteSignedNodeBranch
