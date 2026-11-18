import LogicLineages.PersistentMarking.MarkedConstructorCanonicalOpeningProof
import LogicLineages.PersistentMarking.ProtectedSpineLawTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineObservationProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations HereditaryDomainCode
open ProtectedSpineEnvironment

theorem opened (E : Environment) (Δ : Context) (σ ρ : Ty) (body : Expr) (i : Nat)
    (hi : Δ[i]? = some none)
    (h : Expr.lam σ body ∈ observations E.names E.ports Δ E.target (.arrow σ ρ)) :
    openBody σ (portName E.names i) body ∈
      observations E.names E.ports (openingContext Δ σ i) E.target ρ := by
  rw [MarkedConstructorCanonicalOpeningProof.openingEqFill]
  obtain ⟨stack,q,vs,hocc,hvs,hqtype,hdepth,heq⟩ :=
    (DecisionObservationProof.enumeration E.names E.ports Δ E.target (.arrow σ ρ)
      (.lam σ body)).mp h
  have hfree := DecisionAssignmentProof.freeValues E.names Δ stack vs hvs
  obtain ⟨original,rfl,hbody⟩ := ObservationOpeningProof.reflection vs q σ body hfree heq.symm
  have htype : original.type = ρ := (Ty.arrow.inj hqtype).2
  have hchild := ObservationLambdaProof.occurrenceTrans [] E.target stack (.lam σ original)
    hocc (σ::stack) original (.lam .root)
  have hfill := ObservationPortUpdateProof.fillExact Δ i σ hi
  apply (DecisionObservationProof.enumeration E.names E.ports _ E.target ρ _).mpr
  refine ⟨σ::stack,original,.cons (.free σ (portName E.names i)) vs,hchild,
    ObservationPortUpdateProof.assignmentPrepend E.names Δ stack vs i σ hvs hi,htype,?_,?_⟩
  · simp only [lambdaDepth] at hdepth
    rw [hfill.2.2.2]
    omega
  · rw [hbody]
    exact ObservationOpeningProof.coherence vs σ (portName E.names i) 0 original hfree

end LogicLineages.PersistentMarking.ProtectedSpineObservationProof
