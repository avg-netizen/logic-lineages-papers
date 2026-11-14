module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.OrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilValue (reached : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 count z z reached)) :=
  InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) countStep z
    (Fin.cons reached Fin.elim0) (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons reached Fin.elim0))

theorem queryHit (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 contains (suc z) reached head))) :
    Nonempty (Derivation body Delta
      (programGraph (.composition contains ![.projection 2,.projection 0]) (suc z) ![head,rest,reached])) := by
  apply binaryValue contains (.projection 2) (.projection 0) (suc z) reached head
    ![head,rest,reached] h (projectionValue 2 ![head,rest,reached]) (projectionValue 0 ![head,rest,reached])

theorem queryMiss (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 contains (suc z) reached head).not)) :
    Nonempty (Derivation body Delta
      (programGraph (.composition contains ![.projection 2,.projection 0]) (suc z) ![head,rest,reached]).not) := by
  let A := programGraph (.composition contains ![.projection 2,.projection 0]) (suc z) ![head,rest,reached]
  obtain ⟨hm⟩ := binaryRecover contains (.projection 2) (.projection 0) (suc z) reached head
    ![head,rest,reached] (Nonempty.intro (Derivation.hypothesis (body := body)
      (Gamma := A :: Delta) List.mem_cons_self)) (projectionValue 2 ![head,rest,reached]) (projectionValue 0 ![head,rest,reached])
  obtain ⟨h⟩ := withHyp h A
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination h hm)⟩

theorem hitValue (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 contains (suc z) reached head))) :
    Nonempty (Derivation body Delta (graph3 countStep rest head rest reached)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,reached]
  let query : Program 3 := .composition contains ![.projection 2,.projection 0]
  exact successorBranchIntro (normalize query) (.composition .succ (fun _ : Fin 1 => .projection 1))
    (.projection 1) rest z xs (normalizeAccept query xs (queryHit head rest reached h)) (projectionValue 1 xs)

theorem missValue (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 contains (suc z) reached head).not)) :
    Nonempty (Derivation body Delta (graph3 countStep (suc rest) head rest reached)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,reached]
  let query : Program 3 := .composition contains ![.projection 2,.projection 0]
  have hs : Nonempty (Derivation body Delta
      (programGraph (.composition .succ (fun _ : Fin 1 => .projection 1)) (suc rest) xs)) := by
    apply compositionValue .succ (fun _ : Fin 1 => .projection 1) (suc rest) xs
      (Fin.cons rest Fin.elim0) (InternalControlGraphSupportProof.successorValue (Fin.cons rest Fin.elim0))
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  exact zeroBranchIntro (normalize query) (.composition .succ (fun _ : Fin 1 => .projection 1))
    (.projection 1) (suc rest) xs (normalizeReject query xs (queryMiss head rest reached h)) hs

theorem consHitEquation (raw head tail reached out rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 count rest tail reached)))
    (ho : Nonempty (Derivation body Delta (graph2 count out raw reached)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) reached head))) :
    Nonempty (Derivation body Delta (eqn out rest)) := by
  have hv : Nonempty (Derivation body Delta (graph2 count rest raw reached)) :=
    InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) countStep
      raw head tail rest rest (Fin.cons reached Fin.elim0) hc ht (hitValue head rest reached hm)
  exact valueUnique count out rest ![raw,reached] ho hv

theorem consMissEquation (raw head tail reached out rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 count rest tail reached)))
    (ho : Nonempty (Derivation body Delta (graph2 count out raw reached)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) reached head).not)) :
    Nonempty (Derivation body Delta (eqn out (suc rest))) := by
  have hv : Nonempty (Derivation body Delta (graph2 count (suc rest) raw reached)) :=
    InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) countStep
      raw head tail rest (suc rest) (Fin.cons reached Fin.elim0) hc ht (missValue head rest reached hm)
  exact valueUnique count out (suc rest) ![raw,reached] ho hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.StepProof
