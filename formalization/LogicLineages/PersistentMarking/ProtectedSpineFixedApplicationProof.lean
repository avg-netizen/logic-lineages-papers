import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationCases

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationProof
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets ProtectedSpineFixedApplicationCases
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

theorem forArgs (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hfix : step S E H M = M) (hw : WellFormed E.types E.ports Γ) (args : Args) :
    AuxLaw S E H M Γ args :=
  @Args.rec (fun _ => True) (AuxLaw S E H M Γ)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial)
    (emptyCase S E H M Γ hc hm hw)
    (fun a rest _ ih => consCase S E H M Γ hc hm hfix hw a rest ih) args

theorem exact_FixedApplicationAux : FixedApplicationAux := by
  intro S E H M Γ q args values types τ hc hm hfix hw hv hq hcov ha has
  exact forArgs S E H M Γ hc hm hfix hw args q values types τ hv hq hcov ha has

theorem exact_FixedApplication : FixedApplication := by
  intro S E H M Γ q args τ hc hm hfix hw hq hcov ha has
  cases args with
  | nil =>
    have he : q.type = τ := (ProtectedSpineConcreteInputProof.argumentTypes q.type .nil τ ha).2.symm
    rw [← he]
    simp [call,domainTypes,MarkedConstructorTests.terms,closedCodes,evaluateArgs,apply,concreteOutput,
      ProtectedSpineInterpreter.interpret,ProtectedSpineLaws.codeAt,ProtectedSpineLaws.valueAt]
  | cons a args =>
    exact exact_FixedApplicationAux S E H M Γ q (.cons a args) .nil [] τ hc hm hfix hw
      ⟨.nil,by simp [ProtectedSpineLaws.ArgsCovered,DecisionInventory.auxiliaryArgs,DecisionInventory.headsArgs]⟩
      hq hcov ha has

#print axioms exact_FixedApplicationAux
#print axioms exact_FixedApplication
end LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationProof
