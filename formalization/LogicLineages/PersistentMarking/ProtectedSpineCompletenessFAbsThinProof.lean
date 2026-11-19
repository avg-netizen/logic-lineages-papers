import LogicLineages.PersistentMarking.ProtectedSpineFAbsParameterThinProof
import LogicLineages.PersistentMarking.DecisionClosureBinderProof

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessFAbsThinProof
open Spine NameBridge DecisionPorts DecisionRequests ObservationLambda FiniteDomainSchema
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open ProtectedSpineEnvironment ProtectedSpineFixedApplicationTargets
open MarkedConstructorOperator (step)

theorem fabs {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (σ τ : Ty)
    (bs es : Args) (t : Expr) (i : Nat)
    (hs : PaperTerm S (.marked f (.arrow σ τ) bs es) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ)) (hσ : σ ∈ F.data.types)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M) (hi : firstUnused Γ = some i)
    (hDeriv : PortComparison.Weak S F.data.types F.data.names (fillSlot Γ i σ)
      (.marked f τ bs (es.append (.cons (.free σ (portName F.data.names i)) .nil)))
      (openBody σ (portName F.data.names i) t))
    (ih : WeakGoal F M (fillSlot Γ i σ)
      (.marked f τ bs (es.append (.cons (.free σ (portName F.data.names i)) .nil))) (openBody σ (portName F.data.names i) t)) :
    WeakGoal F M Γ (.marked f (.arrow σ τ) bs es) (.lam σ t) := by
  intro h
  let E := domain F
  let H := F.data.sourceHeads
  let Θ := openingContext Γ σ i
  let x := portName F.data.names i
  let newExtras := es.append (.cons (.free σ x) .nil)
  let r := Expr.marked f τ bs newExtras
  let p := ownerAt S F M Γ f (.arrow σ τ) bs es
  have hp := ProtectedSpineAdequacyOwnerProof.valid S F M Γ f (.arrow σ τ) bs es hm h.1 h.2.1 hs.1
  have hChild := DecisionClosureBinderProof.fabsChild S F Γ σ τ f bs es t i hs ht hi h
  have hEq := MarkedConstructorCanonicalOpeningProof.openingEqFill Γ σ i
  have hActual : Invariant F (.weak Θ r (openBody σ x t)) := by
    change Invariant F (.weak (openingContext Γ σ i) r (openBody σ x t))
    rw [hEq]
    exact hChild
  have hBit : (unfoldedValue S F M Θ r).weak Θ (openBody σ x t) = true := by
    change (unfoldedValue S F M (openingContext Γ σ i) r).weak (openingContext Γ σ i) (openBody σ x t) = true
    rw [hEq]
    exact ih hChild
  have hTypes := ProtectedSpineAdequacyTypingProof.weak S F.data.types F.data.names _ r _ hDeriv
  have hGet := ProtectedSpineAdequacyOwnerProof.previous S F M Θ f τ bs newExtras hm hfix
    hActual.1 hActual.2.1 hTypes.1.1
  have hRoot := rootBits S F M Θ r (openBody σ x t) hm hActual.1 hActual.2.1 hTypes.1.1 hActual.2.2 hTypes.2.2
  have hParam := ProtectedSpineFAbsParameterThinProof.openedParameter S F M Γ f σ τ bs es i hm h.1 hσ
    (ObservationPortUpdateProof.firstSound Γ i hi) h.2.1 hs.1
  have hSpec : MarkedConstructorTargets.FAbsWitness E H M p (.lam σ t) := by
    refine ⟨σ,τ,t,i,concreteOutput S E H M Θ τ (some r),rfl,rfl,
      MarkedConstructorCanonicalOpeningProof.slotEq Γ i hi,?_,hRoot.1.trans hBit⟩
    change StructuralActions.markedAction E H M
      (MarkedConstructorTests.fabsParameter E (ownerAt S F M Γ f (.arrow σ τ) bs es) σ τ i) = _
    rw [hParam]
    exact hGet
  have hTest := (MarkedConstructorFAbsExactProof.fabs E H M p (.lam σ t)).mpr hSpec
  rw [ProtectedSpineAdequacyOwnerProof.rootEq S F M Γ f (.arrow σ τ) bs es hp]
  change MarkedConstructorTests.weakTest S E H M p (.lam σ t) = true
  simp [MarkedConstructorTests.weakTest,hTest]

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessFAbsThinProof
