import LogicLineages.PersistentMarking.NumberedWindowApplicationForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextPathProof

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationForwardChecks
open NumberedWindowApplicationForwardTargets NumberedWindowApplicationMatchChecks
open NumberedWindowAddressApplication NumberedWindowApplicationGraphChecks
open NumberedWindowAddressApplicationTargets NumberedWindowAddressApplicationChecks
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticClassAddressProof NumberedWindowPathWitnessClassCode
open NumberedWindowExternalApplication

theorem exact_ForwardAddressMatching : ExactForwardAddressMatching := by
  intro S K hk source target argument value certificate supplied earlier
  obtain ⟨Γ,ft,i,j,q,r,sourceCode,targetCode,hq,hr,_⟩ :=
    (NumberedWindowArithmeticAllContextPathProof.positive S K source target hk).mp
      ⟨certificate,supplied⟩
  have sourceGraph := earlier
  rw [← sourceCode] at sourceGraph
  have hasLater : ∃ next, graph (fixed S K) target argument next = true := by
    rw [← targetCode]
    cases ft with
    | ground =>
        have applied : application (fixed S K) (encodeAddress ⟨Γ,.ground,i⟩) argument = some value :=
          beq_iff_eq.mp sourceGraph
        rw [exact_DecodedApplication S K] at applied
        unfold decodedApplication at applied
        rw [round] at applied
        cases h : decodeAddress argument <;> simp [h] at applied
    | arrow σ τ =>
        obtain ⟨a,u,k,argumentCode,hu,_,_⟩ :=
          (exact_ClassApplicationGraph S K Γ σ τ hk q i hq argument value).mp sourceGraph
        obtain ⟨nextCode,hnext⟩ := existsCode S K Γ τ hk (appClass hk r u)
        refine ⟨encodeAddress ⟨Γ,τ,nextCode⟩, ?_⟩
        exact (exact_ClassApplicationGraph S K Γ σ τ hk r j hr argument _).mpr
          ⟨a,u,nextCode,argumentCode,hu,rfl,hnext⟩
  obtain ⟨next,later⟩ := hasLater
  obtain ⟨before,output,computed,beforeGraph,transformed⟩ :=
    exact_BackwardAddressMatching S K hk source target argument next certificate supplied later
  have beforeValue : application (fixed S K) source argument = some before :=
    beq_iff_eq.mp beforeGraph
  have expectedValue : application (fixed S K) source argument = some value :=
    beq_iff_eq.mp earlier
  have eq : before = value := Option.some.inj (beforeValue.symm.trans expectedValue)
  subst before
  exact ⟨next,output,computed,later,transformed⟩

#print axioms exact_ForwardAddressMatching

end LogicLineages.PersistentMarking.NumberedWindowApplicationForwardChecks
