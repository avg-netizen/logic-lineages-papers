module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.RowIntroBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.RowIntroCoreProof
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
open RowIntroInductionDefinitions RowIntroInductionSyntaxProof RowIntroBindingProof
open NumericDependencyCross (row rowStep rowEntry)

theorem atPair (raw head tail param out rest node a b entry : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 row rest tail param)))
    (hs : Nonempty (Derivation body Delta (graph3 rowStep out head rest param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node param b)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry param head))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,param]
  have he : Nonempty (Derivation body Delta (programGraph rowEntry entry xs)) :=
    binaryValue InternalPairing.pairing (.projection 2) (.projection 0) entry param head xs hp
      (projectionValue 2 xs) (projectionValue 0 xs)
  have ho := binaryRecover InternalListCodec.consCode rowEntry (.projection 1) out entry rest xs hs he (projectionValue 1 xs)
  apply formulaCases (eqn head b)
  · have hp' := InternalApplicationValidityStackAppendRunProof.rightTransport
      InternalPairing.pairing entry param head b
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hp _)
    have heq := valueUnique InternalPairing.pairing entry node ![param,b] hp' (withHyp hq _)
    exact containsHit out entry rest node (withHyp ho _) (by rw [equalEqn]; exact heq)
  · have hn : Nonempty (Derivation body ((eqn head b).not :: Delta) (equal head b).not) := by
      rw [equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover raw head tail b (numeral 1)
      (withHyp hc _) hn (withHyp hm _)
    have hi := belowRawApply raw tail param rest node a b (withHyp ih _)
      (consTailDescent raw head tail (withHyp hc _))
      (andIntro (andIntro (withHyp hr _) ht) (withHyp hq _))
    exact NumericDependencyCross.SupportProof.memberTail out entry rest node (withHyp ho _) hi

theorem atStep (raw head tail param out rest node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 row rest tail param)))
    (hs : Nonempty (Derivation body Delta (graph3 rowStep out head rest param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node param b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  apply programCases InternalPairing.pairing (Fin.cons param (Fin.cons head Fin.elim0)) _
  intro beta j Theta entry hj hp
  simp only [result,conjunctionRename,eqnRelabel,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hp
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
  exact atPair (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (rest.relabel j) (node.relabel j) (a.relabel j) (b.relabel j) entry
    ihj hcj hrj hsj hmj hqj hp

theorem consCore (raw head tail param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 row out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node param b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  have hs := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 1) rowStep
    raw head tail out (Fin.cons param Fin.elim0) hc hv
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 1) rowStep
    out head tail (Fin.cons param Fin.elim0) _ hs
  intro beta j Theta rest hj hr hstep
  simp only [consTermRename, emptyRename] at hr hstep
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
    (hv : Nonempty (Derivation body Delta (graph2 row out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node param b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  apply OriginalContextInsertionLengthProof.listCases raw _
  · have hm0 := headTransport contains (numeral 1) raw z (Fin.cons b Fin.elim0)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm _)
    obtain ⟨hn⟩ := valueUnique contains (numeral 1) z ![z,b] hm0 (containsNil b)
    exact ⟨Derivation.explosion (sucNeZeroApply hn)⟩
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.RowIntroCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.RowIntroCoreProof
