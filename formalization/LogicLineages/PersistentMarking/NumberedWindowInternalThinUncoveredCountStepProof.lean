module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountStepProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2 graph3)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (binaryValue binaryRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro zeroBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalThinUncoveredCount

private theorem withHyp {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    {f : Formula α} (h : Nonempty (Derivation body Γ f)) (p : Formula α) :
    Nonempty (Derivation body (p :: Γ) f) := by
  obtain ⟨h⟩ := h
  exact ⟨addHyp h p⟩

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilValue (reached : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 count z z reached)) :=
  ID1Completion.InternalRawListRecursionProof.nilValue (ID1Completion.InternalAcceptance.constantZero 1) countStep z
    (Fin.cons reached Fin.elim0) (ID1Completion.InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons reached Fin.elim0))

theorem queryHit (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 scratchMember (suc z) reached head))) :
    Nonempty (Derivation body Delta
      (programGraph (.composition scratchMember ![.projection 2,.projection 0]) (suc z) ![head,rest,reached])) := by
  apply binaryValue scratchMember (.projection 2) (.projection 0) (suc z) reached head
    ![head,rest,reached] h (projectionValue 2 ![head,rest,reached]) (projectionValue 0 ![head,rest,reached])

theorem queryMiss (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 scratchMember (suc z) reached head).not)) :
    Nonempty (Derivation body Delta
      (programGraph (.composition scratchMember ![.projection 2,.projection 0]) (suc z) ![head,rest,reached]).not) := by
  let A := programGraph (.composition scratchMember ![.projection 2,.projection 0]) (suc z) ![head,rest,reached]
  obtain ⟨hm⟩ := binaryRecover scratchMember (.projection 2) (.projection 0) (suc z) reached head
    ![head,rest,reached] (Nonempty.intro (Derivation.hypothesis (body := body)
      (Gamma := A :: Delta) List.mem_cons_self)) (projectionValue 2 ![head,rest,reached]) (projectionValue 0 ![head,rest,reached])
  obtain ⟨h⟩ := withHyp h A
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination h hm)⟩

theorem hitValue (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 scratchMember (suc z) reached head))) :
    Nonempty (Derivation body Delta (graph3 countStep rest head rest reached)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,reached]
  let query : Program 3 := .composition scratchMember ![.projection 2,.projection 0]
  exact successorBranchIntro (normalize query) (.composition .succ (fun _ : Fin 1 => .projection 1))
    (.projection 1) rest z xs (normalizeAccept query xs (queryHit head rest reached h)) (projectionValue 1 xs)

theorem missValue (head rest reached : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 scratchMember (suc z) reached head).not)) :
    Nonempty (Derivation body Delta (graph3 countStep (suc rest) head rest reached)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,reached]
  let query : Program 3 := .composition scratchMember ![.projection 2,.projection 0]
  have hs : Nonempty (Derivation body Delta
      (programGraph (.composition .succ (fun _ : Fin 1 => .projection 1)) (suc rest) xs)) := by
    apply compositionValue .succ (fun _ : Fin 1 => .projection 1) (suc rest) xs
      (Fin.cons rest Fin.elim0) (ID1Completion.InternalControlGraphSupportProof.successorValue (Fin.cons rest Fin.elim0))
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  exact zeroBranchIntro (normalize query) (.composition .succ (fun _ : Fin 1 => .projection 1))
    (.projection 1) (suc rest) xs (normalizeReject query xs (queryMiss head rest reached h)) hs

theorem consHitEquation (raw head tail reached out rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ID1Completion.InternalListCodec.consCode raw head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 count rest tail reached)))
    (ho : Nonempty (Derivation body Delta (graph2 count out raw reached)))
    (hm : Nonempty (Derivation body Delta (graph2 scratchMember (suc z) reached head))) :
    Nonempty (Derivation body Delta (eqn out rest)) := by
  have hv : Nonempty (Derivation body Delta (graph2 count rest raw reached)) :=
    ID1Completion.InternalRawListRecursionProof.consValue (ID1Completion.InternalAcceptance.constantZero 1) countStep
      raw head tail rest rest (Fin.cons reached Fin.elim0) hc ht (hitValue head rest reached hm)
  exact valueUnique count out rest ![raw,reached] ho hv

theorem consMissEquation (raw head tail reached out rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ID1Completion.InternalListCodec.consCode raw head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 count rest tail reached)))
    (ho : Nonempty (Derivation body Delta (graph2 count out raw reached)))
    (hm : Nonempty (Derivation body Delta (graph2 scratchMember (suc z) reached head).not)) :
    Nonempty (Derivation body Delta (eqn out (suc rest))) := by
  have hv : Nonempty (Derivation body Delta (graph2 count (suc rest) raw reached)) :=
    ID1Completion.InternalRawListRecursionProof.consValue (ID1Completion.InternalAcceptance.constantZero 1) countStep
      raw head tail rest (suc rest) (Fin.cons reached Fin.elim0) hc ht (missValue head rest reached hm)
  exact valueUnique count out (suc rest) ![raw,reached] ho hv

#print axioms nilValue
#print axioms consHitEquation
#print axioms consMissEquation
end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountStepProof
