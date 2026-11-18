import LogicLineages.PersistentMarking.ProtectedSpineCompletenessTargets
import LogicLineages.PersistentMarking.PortLambdaStateProof
import LogicLineages.PersistentMarking.PortTermStateProof
import LogicLineages.PersistentMarking.ProtectedSpineStrictMarkProof

namespace LogicLineages.PersistentMarking.ProtectedSpineOpeningCodeProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics PortNormalization
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineFixedApplicationTargets

theorem literalCodeEq (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (σ : Ty) (x : Nat) (hw : WellFormed E.types E.ports Γ) :
    codeAt E σ (evaluate S E H M (.free σ x)) Γ ⟨[],[]⟩ = literalCode E Γ σ x :=
  HereditaryCodeReconstructionProof.reconstruct E σ Γ (literalCode E Γ σ x)
    (MarkedConstructorLiteralProof.literalRetained E Γ σ x hw)

theorem singletonCode (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (σ : Ty) (x : Nat) (hw : WellFormed E.types E.ports Γ) :
    closedCodes S E H M Γ (.cons (.free σ x) .nil) = [(σ,literalCode E Γ σ x)] := by
  change [(σ,codeAt E σ (evaluate S E H M (.free σ x)) Γ ⟨[],[]⟩)] = _
  rw [literalCodeEq S E H M Γ σ x hw]

theorem bodyValue (S : Signature) (F : Inputs S) (M : Code)
    (Γ : Context) (σ τ : Ty) (body : Expr) (i : Nat)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ) (hi : Γ[i]? = some (some σ))
    (ht : Typed (EmptyContext.push σ) body τ)
    (hcov : Covered (domain F) F.data.sourceHeads body) :
    ValueEq (domain F) τ Γ
      (valueAt (evaluate S (domain F) F.data.sourceHeads M body) Γ
        ⟨[],[(σ,literalCode (domain F) Γ σ (portName F.data.names i))]⟩)
      (unfoldedValue S F M Γ (openBody σ (portName F.data.names i) body)) := by
  let E := domain F
  let H := F.data.sourceHeads
  let x := portName F.data.names i
  let vs : Args := .cons (.free σ x) .nil
  have hPort := DecisionObservedTypesProof.portUniverse F.data.types F.data.names H Γ σ (.free σ x)
    (PortTermStateProof.closed S F) hw.2 ⟨i,hi,rfl⟩
  have hCovs : ArgsCovered E H vs :=
    ProtectedSpineFixedApplicationCases.appendCoverage E H (.free σ x) .nil ⟨hPort.1,hPort.2.1⟩
      (by simp [ArgsCovered,auxiliaryArgs,headsArgs])
  have hv : ProtectedSpineBoundTargets.BoundImages E H vs [σ] := ⟨.cons .free .nil,hCovs⟩
  have hAgree := ProtectedSpineBoundSubstitutionProof.exact_BoundSubstitution S E H M vs [σ] [] body τ
    (prefixClosed S F) hm hv ht hcov
  have h := hAgree.value Γ ⟨[],closedCodes S E H M Γ vs⟩ ⟨[],[]⟩
    (ProtectedSpineConcreteInputProof.boundValid S E H M Γ vs [σ] (prefixClosed S F) hm hw hv)
    (ProtectedSpineConcreteInputProof.emptyValid E Γ hw)
    (ProtectedSpineConcreteInputProof.boundRelation S E H M Γ vs)
  rw [show closedCodes S E H M Γ vs = [(σ,literalCode E Γ σ x)]
    from singletonCode S E H M Γ σ x hw] at h
  exact h

end LogicLineages.PersistentMarking.ProtectedSpineOpeningCodeProof
