module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.RowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open CrossInductionDefinitions CrossInductionSyntaxProof CrossBindingProof

theorem atRow (raw head tail param out rest node a b rowValue : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 cross rest tail param)))
    (hs : Nonempty (Derivation body Delta (graph3 crossStep out head rest param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b)))
    (hrow : Nonempty (Derivation body Delta (graph2 row rowValue param head))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,param]
  have he : Nonempty (Derivation body Delta (programGraph currentRow rowValue xs)) :=
    binaryValue row (.projection 2) (.projection 0) rowValue param head xs hrow
      (projectionValue 2 xs) (projectionValue 0 xs)
  have ho := binaryRecover InternalApplicationValidityStackAppend.append currentRow (.projection 1)
    out rowValue rest xs hs he (projectionValue 1 xs)
  obtain ⟨hd⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation rowValue rest out node ho hm
  let L := graph2 contains (numeral 1) rowValue node
  let R := graph2 contains (numeral 1) rest node
  have hl := RowProof.projection param head rowValue node a b (withHyp hrow L)
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hq L)
  obtain ⟨ha⟩ := andLeft hl
  have hmLeft := containsHit raw head tail a (withHyp hc L)
    (by rw [equalEqn]; exact ⟨symm ha⟩)
  obtain ⟨hleft⟩ := andIntro hmLeft (andRight hl)
  have ht := belowRawApply raw tail param rest node a b (withHyp ih R)
    (consTailDescent raw head tail (withHyp hc R))
    (andIntro (andIntro (withHyp hr R) ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hq R))
  obtain ⟨hright⟩ := andIntro (SupportProof.memberTail raw head tail a (withHyp hc R) (andLeft ht)) (andRight ht)
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hleft) (Derivation.implicationIntroduction hright)⟩

theorem atStep (raw head tail param out rest node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 cross rest tail param)))
    (hs : Nonempty (Derivation body Delta (graph3 crossStep out head rest param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  apply programCases row (Fin.cons param (Fin.cons head Fin.elim0)) _
  intro beta j Theta rowValue hj hrow
  simp only [result,conjunctionRename,eqnRelabel,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hrow
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at ihj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hcj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hrj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hsj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hmj
  have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hqj
  exact atRow (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (rest.relabel j) (node.relabel j) (a.relabel j) (b.relabel j) rowValue
    ihj hcj hrj hsj hmj hqj hrow

theorem consCore (raw head tail param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 cross out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  have hs := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 1) crossStep
    raw head tail out (Fin.cons param Fin.elim0) hc hv
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 1) crossStep
    out head tail (Fin.cons param Fin.elim0) _ hs
  intro beta j Theta rest hj hr hstep
  simp only [result,conjunctionRename,eqnRelabel,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at ihj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hcj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hmj
  have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hqj
  exact atStep (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) rest (node.relabel j) (a.relabel j) (b.relabel j)
    ihj hcj hr hstep hmj hqj

theorem core (raw param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hv : Nonempty (Derivation body Delta (graph2 cross out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  apply OriginalContextInsertionLengthProof.listCases raw _
  · exact SupportProof.nilImpossible crossStep raw param out node _
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _) (withHyp hm _)
  · intro beta j Theta head tail hj hc
    simp only [result,conjunctionRename,eqnRelabel,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at ihj
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hvj
    have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hmj
    have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hqj
    exact consCore (raw.relabel j) head tail (param.relabel j) (out.relabel j)
      (node.relabel j) (a.relabel j) (b.relabel j) ihj hc hvj hmj hqj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossCoreProof
