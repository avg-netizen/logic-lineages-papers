import LogicLineages.PersistentMarking.NumberedWindowExternalLambdaComputabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalLambdaEdgesChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalInstancePathChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalLambdaComputabilityProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessChecks NumberedWindowExternalInstance
open NumberedWindowExternalApplication NumberedWindowExternalApplicationChecks NumberedWindowExternalLambda
open NumberedWindowExternalComputability NumberedWindowExternalComputabilityChecks
open NumberedWindowExternalTypeFactsChecks NumberedWindowExternalLambdaEdgesChecks
open NumberedWindowExternalInstancePathChecks NumberedWindowExternalLambdaComputabilityTargets

theorem literal : InstanceClassLiteral := by
  intro S K C σ τ hk v u
  rfl

theorem reducts : AppliedLambdaReducts := by
  intro S K C σ τ hk hτ v u out step
  rcases exact_LambdaApplicationEdges S K C σ τ hk hτ v u out step with h | h | h | ⟨a,b,ea,eb,e⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · subst v
    subst u
    exact .inr (.inr (.inr e))

private theorem introAcc {S K Γ σ τ} (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K)
    {v : Class S K ((finiteC Γ).push σ) τ} (a : Acc (fun w v => RS S K ((finiteC Γ).push σ) τ v w) v) :
    (∀ u : Class S K (finiteC Γ) σ, ComputableClass S K Γ hk σ u →
      ComputableClass S K Γ hk τ (instanceClass hk v u)) →
    ComputableClass S K Γ hk (.arrow σ τ) (lamClass hk hτ v) := by
  induction a with
  | intro v _ ih =>
    intro allInst u hu
    apply exact_NeutralComputability S K Γ τ hk _ (NumberedWindowExternalNeutralChecks.exact_NonLambdaApplicationClass
      S K (finiteC Γ) σ τ hk (lamClass hk hτ v) u)
    intro out step
    rcases reducts S K (finiteC Γ) σ τ hk hτ v u out step with bot | ⟨b,hb,rfl⟩ | ⟨w,path,rfl⟩ | rfl
    · exact exact_BottomComputability S K Γ τ hk out bot
    · exact exact_BottomComputability S K Γ (.arrow σ τ) hk b hb u hu
    · apply ih w (.one path) _ u hu
      intro z hz
      rcases exact_InstanceClassEdgeOrEqual S K (finiteC Γ) σ τ hk v w z path with p | e
      · exact exact_ComputableDirectDescendants S K Γ τ hk _ _ p (allInst z hz)
      · exact e ▸ allInst z hz
    · exact allInst u hu

theorem computableLambda : ComputableLambda := by
  intro S K Γ σ τ hk hτ v allInst
  apply introAcc hk hτ (v := v) _ allInst
  refine Quot.inductionOn v ?_ allInst
  intro body inst
  let i := (NumberedWindowPrimaryCoverSyntax.termBounds body.val).numeral+1
  let u : WindowCarrier S K (finiteC Γ) σ :=
    ⟨.free σ i, .free, NumberedWindowApplicationDomainProof.arrowLeft hk hτ,by intro f hf; cases hf⟩
  have hu := exact_VariableComputability S K Γ σ hk (classOf u) ⟨u,⟨i,Or.inl rfl⟩,rfl⟩
  let x := instanceClass hk (classOf body) (classOf u)
  obtain ⟨j,hj⟩ := (exact_ActualClassCodeFibers S K Γ τ hk).1 x
  have acc := (exact_ScalarClassAccessibility S K Γ τ hk x j hj).mp
    (exact_ComputabilityImpliesScalarI S K Γ τ hk x j hj (inst (classOf u) hu))
  exact exact_FreeInstanceReflectsAccessibility S K (finiteC Γ) σ τ hk (classOf body) u i rfl acc

end LogicLineages.PersistentMarking.NumberedWindowExternalLambdaComputabilityProof
