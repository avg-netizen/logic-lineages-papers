module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairIntroBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairIntroCoreProof
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
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open PairIntroInductionDefinitions PairIntroInductionSyntaxProof PairIntroBindingProof

theorem atValues (raw head tail param out rest node a b mappedHead : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 pairRoots rest tail param)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedHead rest)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node param b)))
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mappedHead param head))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  apply formulaCases (eqn head b)
  · have hh' : Nonempty (Derivation body ((eqn head b) :: Delta)
        (graph2 InternalPairing.pairing mappedHead param b)) := by
      unfold graph2 programGraph at hh ⊢
      apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2
        ((eqn head b) :: Delta) (OrdinaryArithmetic.graphFormula InternalPairing.pairing) mappedHead ![param,head] ![param,b]
      · intro i
        fin_cases i
        · rw [InternalSourceInversionSupportProof.onEquality]
          exact ⟨refl param⟩
        · rw [InternalSourceInversionSupportProof.onEquality]
          exact ⟨Derivation.hypothesis List.mem_cons_self⟩
      · exact withHyp hh _
    have heq := valueUnique InternalPairing.pairing mappedHead node ![param,b] hh' (withHyp hq _)
    exact containsHit out mappedHead rest node (withHyp ho _) (by rw [equalEqn]; exact heq)
  · have hn : Nonempty (Derivation body ((eqn head b).not :: Delta) (equal head b).not) := by
      rw [equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover raw head tail b (numeral 1)
      (withHyp hc _) hn (withHyp hm _)
    have hi := belowRawApply raw tail param rest node a b (withHyp ih _)
      (consTailDescent raw head tail (withHyp hc _))
      (andIntro (andIntro (withHyp hr _) ht) (withHyp hq _))
    exact NumericDependencyCross.SupportProof.memberTail out mappedHead rest node (withHyp ho _) hi

theorem consCore (raw head tail param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 pairRoots out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node param b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  let qs : Fin 2 → Program 3 := ![.composition InternalPairing.pairing ![.projection 2,.projection 0],
    .composition pairRoots ![.projection 1,.projection 2] ]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs ![head,tail,param] _
  intro beta j ys Theta hj hvals
  simp only [result,PairImageProof.imageRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  let xs : Fin 3 → OTerm beta := ![head.relabel j,tail.relabel j,param.relabel j]
  have hx : (fun i => (![head,tail,param] i).relabel j) = xs := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hvals
  have hh := binaryRecover InternalPairing.pairing (.projection 2) (.projection 0)
    (ys 0) (param.relabel j) (head.relabel j) xs (hvals 0) (projectionValue 2 xs) (projectionValue 0 xs)
  have hr := binaryRecover pairRoots (.projection 1) (.projection 2)
    (ys 1) (tail.relabel j) (param.relabel j) xs (hvals 1) (projectionValue 1 xs) (projectionValue 2 xs)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at ihj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hqj
  have ho := PairRecursionProof.consForward (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (ys 0) (ys 1) (out.relabel j) hcj hh hr hvj
  exact atValues (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (ys 1) (node.relabel j) (a.relabel j) (b.relabel j) (ys 0) ihj hcj hr ho hmj hqj hh

theorem core (raw param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hv : Nonempty (Derivation body Delta (graph2 pairRoots out raw param)))
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairIntroCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairIntroCoreProof
