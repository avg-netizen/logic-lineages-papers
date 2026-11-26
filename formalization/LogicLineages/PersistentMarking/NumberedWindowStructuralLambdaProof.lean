import LogicLineages.PersistentMarking.NumberedWindowStructuralEnvironmentProof
import LogicLineages.PersistentMarking.NumberedWindowExternalLambdaComputabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowBindingPushProof

namespace LogicLineages.PersistentMarking.NumberedWindowStructuralLambdaProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowStructuralComputabilityTargets
open NumberedWindowExternalLambda NumberedWindowExternalInstance NumberedWindowExternalSubstitutionTargets
open NumberedWindowExternalComputability NumberedWindowExternalLambdaComputabilityChecks
open NumberedWindowStructuralEnvironmentProof
open NumberedWindowPreservationGuardProof (lamBody)
open NumberedWindowApplicationDomainProof (rootInWindow)

theorem lambda {S K Γ C σ τ body} (hk : DecisionSourceUniverse.Closed K) (values : NArgs)
    (hSource : InWindow S K C (.arrow σ τ) (.lam σ body)) (hEnv : Environment S K Γ hk C values)
    (ih : ∀ vals, Environment S K Γ hk (C.push σ) vals →
      TypedComputable S K Γ hk τ (substitute vals 0 body)) :
    TypedComputable S K Γ hk (.arrow σ τ) (substitute values 0 (.lam σ body)) := by
  have hWindow : InWindow S K (finiteC Γ) (.arrow σ τ) (.lam σ (substitute values 1 body)) :=
    NumberedWindowPreservationSubstitutionProof.term S K hk values 0 C (finiteC Γ) _ _
      hSource (compatible hEnv)
  let value : WindowCarrier S K ((finiteC Γ).push σ) τ := ⟨substitute values 1 body, lamBody hWindow⟩
  have hArrow := rootInWindow hSource
  refine ⟨hWindow, ?_⟩
  change ComputableClass S K Γ hk (.arrow σ τ) (lamClass hk hArrow (classOf value))
  apply exact_ComputableLambda S K Γ σ τ hk hArrow (classOf value)
  intro u
  refine Quot.inductionOn u ?_
  intro arg hArg
  have hLiteralArg : TypedComputable S K Γ hk σ arg.val := ⟨arg.property, hArg⟩
  obtain ⟨hSub, hComputable⟩ := ih (.cons arg.val values) (extend hEnv hLiteralArg)
  let result : WindowCarrier S K (finiteC Γ) τ := ⟨substitute (.cons arg.val values) 0 body, hSub⟩
  have hTerm : bodyInstance hk value arg = result :=
    Subtype.ext (NumberedWindowBindingPushProof.push arg.val values 0 body)
  change ComputableClass S K Γ hk τ (classOf (bodyInstance hk value arg))
  rw [hTerm]
  exact hComputable

end LogicLineages.PersistentMarking.NumberedWindowStructuralLambdaProof
