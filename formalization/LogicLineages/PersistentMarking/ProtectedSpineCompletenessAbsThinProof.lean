import LogicLineages.PersistentMarking.ProtectedSpineOpeningCodeThinProof
import LogicLineages.PersistentMarking.ProtectedSpineStrictFieldLambdaStep
import LogicLineages.PersistentMarking.DecisionClosureBinderProof

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessAbsThinProof
open Spine NameBridge DecisionPorts DecisionRequests ObservationLambda FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter

theorem abs {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (σ τ : Ty)
    (s t : Expr) (i : Nat) (hs : PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hi : firstUnused Γ = some i)
    (ih : WeakGoal F M (fillSlot Γ i σ) (openBody σ (portName F.data.names i) s)
      (openBody σ (portName F.data.names i) t)) :
    WeakGoal F M Γ (.lam σ s) (.lam σ t) := by
  intro h
  let E := domain F
  let H := F.data.sourceHeads
  let Θ := openingContext Γ σ i
  let x := portName F.data.names i
  have hChild := DecisionClosureBinderProof.absChild S F Γ σ τ s t i hs ht hi h
  have hBody : Typed (EmptyContext.push σ) s τ := by
    cases hs.1 with
    | lam h => exact h
  have hCovered := ProtectedSpineCoverageProof.lambdaBody E H σ s (sourceCovered S F Γ (.lam σ s) h.2.1)
  have hEq := MarkedConstructorCanonicalOpeningProof.openingEqFill Γ σ i
  have hu := ObservationPortUpdateProof.firstSound Γ i hi
  have hOccupied : Θ[i]? = some (some σ) := by
    change (openingContext Γ σ i)[i]? = some (some σ)
    rw [hEq]
    exact (ObservationPortUpdateProof.fillExact Γ i σ hu).2.2.1
  have hW : WellFormed F.data.types F.data.ports Θ := by
    change WellFormed _ _ (openingContext Γ σ i)
    rw [hEq]
    exact hChild.1
  have hv := ProtectedSpineOpeningCodeThinProof.bodyValue S F M Θ σ τ s i hm hW hOccupied hBody hCovered
  have hTyped := ElementarySupportProof.openingPaper S σ τ x t ht
  have hType := SpineShiftProof.annotationExact _ _ _ hTyped.1
  have hObs : openBody σ x t ∈ DecisionObservations.observations E.names E.ports Θ E.target τ := by
    have hO := hChild.2.2
    change openBody σ x t ∈ DecisionObservations.observations E.names E.ports (fillSlot Γ i σ)
      E.target (openBody σ x t).type at hO
    rw [hType] at hO
    change openBody σ x t ∈ DecisionObservations.observations E.names E.ports (openingContext Γ σ i) E.target τ
    rw [hEq]
    exact hO
  have hField := ((hv Θ hW (DecisionPortsProof.extensionRefl Θ)).2.1 (openBody σ x t) hObs).1
  have hVal : (unfoldedValue S F M Θ (openBody σ x s)).weak Θ (openBody σ x t) = true := by
    change (unfoldedValue S F M (openingContext Γ σ i) (openBody σ x s)).weak
      (openingContext Γ σ i) (openBody σ x t) = true
    rw [hEq]
    exact ih hChild
  change (valueAt (evaluate S E H M (.lam σ s)) Γ ⟨[],[]⟩).weak Γ (.lam σ t) = true
  rw [ProtectedSpineStrictFieldLambdaStep.lambdaWeak,
    ProtectedSpineLambdaFieldProof.fieldEq E σ (evaluate S E H M s) Γ Γ ⟨[],[]⟩ false t i
      (MarkedConstructorCanonicalOpeningProof.slotEq Γ i hi)]
  exact hField.trans hVal

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessAbsThinProof
