module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalAcceptanceNormalizationProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open PrimaryExpansion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consContainsTail (out head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) tail needle))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) out needle)) := by
  let A := equal head needle
  apply formulaCases A
  · exact containsHit out head tail needle (withHyp hc A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact containsMiss out head tail needle (suc z) (withHyp hc A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not)

theorem queryValue (E : Program 3) (head rest reached parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (anyEdge E) (suc z) reached head parameter))) :
    Nonempty (Derivation body Delta (programGraph
      (.composition (anyEdge E) ![.projection 2,.projection 0,.projection 3]) (suc z)
      ![head,rest,reached,parameter])) := by
  apply compositionValue (anyEdge E) ![.projection 2,.projection 0,.projection 3]
    (suc z) ![head,rest,reached,parameter] ![reached,head,parameter] he
  intro i
  exact Fin.cases (projectionValue (2 : Fin 4) ![head,rest,reached,parameter])
    (Fin.cases (projectionValue (0 : Fin 4) ![head,rest,reached,parameter])
      (Fin.cases (projectionValue (3 : Fin 4) ![head,rest,reached,parameter]) (fun j => Fin.elim0 j))) i

theorem acceptedCons (E : Program 3) (out head rest reached parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (anyEdge E) (suc z) reached head parameter)))
    (hs : Nonempty (Derivation body Delta (graph4 (filterStep E) out head rest reached parameter))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head rest)) := by
  let xs : Fin 4 → OTerm alpha := ![head,rest,reached,parameter]
  let query : Program 4 := .composition (anyEdge E) ![.projection 2,.projection 0,.projection 3]
  have hb := successorBranchElim (normalize query) (.projection 1)
    (.composition InternalListCodec.consCode ![.projection 0,.projection 1]) out z xs
    (normalizeAccept query xs (queryValue E head rest reached parameter he)) hs
  exact binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1) out head rest xs
    hb (projectionValue 0 xs) (projectionValue 1 xs)

theorem stepTail (E : Program 3) (out head rest reached parameter needle : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph4 (filterStep E) out head rest reached parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) rest needle))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) out needle)) := by
  let xs : Fin 4 → OTerm alpha := ![head,rest,reached,parameter]
  let query : Program 4 := .composition (anyEdge E) ![.projection 2,.projection 0,.projection 3]
  let A := programGraph query (suc z) xs
  apply formulaCases A
  · have hb := successorBranchElim (normalize query) (.projection 1)
      (.composition InternalListCodec.consCode ![.projection 0,.projection 1]) out z xs
      (normalizeAccept query xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hs A)
    have hc := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1) out head rest xs
      hb (projectionValue 0 xs) (projectionValue 1 xs)
    exact consContainsTail out head rest needle hc (withHyp hm A)
  · have hb := zeroBranchElim (normalize query) (.projection 1)
      (.composition InternalListCodec.consCode ![.projection 0,.projection 1]) out xs
      (normalizeReject query xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hs A.not)
    obtain ⟨hu⟩ := valueUnique (.projection (1 : Fin 4)) out rest xs hb (projectionValue 1 xs)
    exact headTransport contains (suc z) rest out (Fin.cons needle Fin.elim0) ⟨symm hu⟩ (withHyp hm A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
