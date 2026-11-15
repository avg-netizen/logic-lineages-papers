module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open Continuation20261114
open SyntaxProof SupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroCore (out index : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 range out z))) :
    Nonempty (Derivation body Delta (result z out index)) := by
  have he := valueUnique range out z ![z] hg zeroValue
  let M := graph2 contains (numeral 1) out index
  have hm : Nonempty (Derivation body (M :: Delta) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz := headTransport contains (numeral 1) out z (Fin.cons index Fin.elim0) (withHyp he M) hm
  obtain ⟨hf⟩ := nilImpossible index hz
  have forward : Nonempty (Derivation body Delta (M.imp (InternalLessThan.strictLess index z))) :=
    ⟨Derivation.implicationIntroduction (Derivation.explosion hf)⟩
  obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha index
  have backward : Nonempty (Derivation body Delta ((InternalLessThan.strictLess index z).imp M)) := by
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    exact Derivation.explosion (Derivation.implicationElimination
      (weakenClosed hn (InternalLessThan.strictLess index z :: Delta)) (Derivation.hypothesis List.mem_cons_self))
  exact andIntro forward backward

theorem atAppend (bound previous one out index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound)))
    (hp : Nonempty (Derivation body Delta (graph1 range previous bound)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode one bound z)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out previous one))) :
    Nonempty (Derivation body Delta (result (suc bound) out index)) := by
  let M := graph2 contains (numeral 1) out index
  let L := graph2 contains (numeral 1) previous index
  let R := graph2 contains (numeral 1) one index
  let Q := InternalLessThan.strictLess index bound
  let E := eqn index bound
  let N := InternalLessThan.strictLess index (suc bound)
  have ih := rowApply bound previous index hr hp
  obtain ⟨ihf⟩ := andLeft ih
  obtain ⟨ihb⟩ := andRight ih
  have split := PrimaryExpansionSoundness.AppendProof.appendPreservation previous one out index
    (withHyp ha M) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨split⟩ := split
  have hl : Nonempty (Derivation body (L :: M :: Delta) N) := lessNext index bound
    ⟨Derivation.implicationElimination (InternalBetaTotalityProof.addHyp
      (InternalBetaTotalityProof.addHyp ihf M) L) (Derivation.hypothesis List.mem_cons_self)⟩
  have he := singletonMember one bound index (withHyp (withHyp hc M) R)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := he
  have hrn : Derivation body (R :: M :: Delta) N := InternalQuotientComparisonProof.equalToNext he
  obtain ⟨hl⟩ := hl
  have forward : Nonempty (Derivation body Delta (M.imp N)) :=
    ⟨Derivation.implicationIntroduction (InternalBetaTotalityProof.disjunctionElimination split
      (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hrn))⟩
  obtain ⟨hs⟩ := nextSplit index bound
    (Delta := N :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hprev : Nonempty (Derivation body (Q :: N :: Delta) L) :=
    ⟨Derivation.implicationElimination (InternalBetaTotalityProof.addHyp
      (InternalBetaTotalityProof.addHyp ihb N) Q) (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨hleft⟩ := PrimaryExpansion.PreservationProof.appendPreservation previous one out index
    (withHyp (withHyp ha N) Q) hprev
  have hsingle := containsHit one bound z index (withHyp (withHyp hc N) E)
    (by rw [equalEqn]; exact ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩)
  obtain ⟨hright⟩ := PrimaryEdgeInclusion.AppendRightProof.appendPreservation previous one out index
    (withHyp (withHyp ha N) E) hsingle
  have backward : Nonempty (Derivation body Delta (N.imp M)) :=
    ⟨Derivation.implicationIntroduction (InternalBetaTotalityProof.disjunctionElimination hs
      (Derivation.implicationIntroduction hleft) (Derivation.implicationIntroduction hright))⟩
  exact andIntro forward backward

theorem atSingleton (bound previous one out index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound)))
    (hp : Nonempty (Derivation body Delta (graph1 range previous bound)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode one bound z)))
    (hg : Nonempty (Derivation body Delta (graph1 range out (suc bound)))) :
    Nonempty (Derivation body Delta (result (suc bound) out index)) := by
  apply InternalAcceptanceSupportProof.programCases InternalApplicationValidityStackAppend.append
    (Fin.cons previous (Fin.cons one Fin.elim0)) _
  intro beta j Theta joined hj ha
  rw [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at ha
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [rowRename,graph1Rename,graph2Rename,zRelabel,sucRelabel] at hrj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [rowRename,graph1Rename,graph2Rename,zRelabel,sucRelabel] at hpj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [rowRename,graph1Rename,graph2Rename,zRelabel,sucRelabel] at hcj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [rowRename,graph1Rename,graph2Rename,zRelabel,sucRelabel] at hgj
  have hv := successorValue (bound.relabel j) (previous.relabel j) (one.relabel j) joined hpj hcj ha
  obtain ⟨he⟩ := valueUnique range joined (out.relabel j) ![suc (bound.relabel j)] hv hgj
  have hao := outputTransport InternalApplicationValidityStackAppend.append joined (out.relabel j)
    (Fin.cons (previous.relabel j) (Fin.cons (one.relabel j) Fin.elim0)) ⟨he⟩ ha
  exact atAppend (bound.relabel j) (previous.relabel j) (one.relabel j) (out.relabel j)
    (index.relabel j) hrj hpj hcj hao

theorem atPrevious (bound previous out index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound)))
    (hp : Nonempty (Derivation body Delta (graph1 range previous bound)))
    (hg : Nonempty (Derivation body Delta (graph1 range out (suc bound)))) :
    Nonempty (Derivation body Delta (result (suc bound) out index)) := by
  apply InternalAcceptanceSupportProof.programCases InternalListCodec.consCode
    (Fin.cons bound (Fin.cons z Fin.elim0)) _
  intro beta j Theta one hj hc
  rw [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hc
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [rowRename,graph1Rename,sucRelabel] at hrj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [rowRename,graph1Rename,sucRelabel] at hpj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [rowRename,graph1Rename,sucRelabel] at hgj
  exact atSingleton (bound.relabel j) (previous.relabel j) one (out.relabel j)
    (index.relabel j) hrj hpj hc hgj

theorem succCore (bound out index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound)))
    (hg : Nonempty (Derivation body Delta (graph1 range out (suc bound)))) :
    Nonempty (Derivation body Delta (result (suc bound) out index)) := by
  apply InternalAcceptanceSupportProof.programCases range (Fin.cons bound Fin.elim0) _
  intro beta j Theta previous hj hp
  rw [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hp
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [rowRename,graph1Rename,sucRelabel] at hrj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [rowRename,graph1Rename,sucRelabel] at hgj
  exact atPrevious (bound.relabel j) previous (out.relabel j) (index.relabel j) hrj hp hgj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.CoreProof
