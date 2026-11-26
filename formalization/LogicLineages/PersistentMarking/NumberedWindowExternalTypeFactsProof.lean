import LogicLineages.PersistentMarking.NumberedWindowExternalAtomicClassesProof
import LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessChecks
open NumberedWindowExternalApplication NumberedWindowExternalApplicationChecks
open NumberedWindowExternalNeutralTargets NumberedWindowExternalNeutralChecks
open NumberedWindowExternalComputability NumberedWindowExternalComputabilityProof
open NumberedWindowExternalTypeFactsTargets NumberedWindowExternalAtomicClassesProof

private structure Facts (S : Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (τ : Ty) : Prop where
  neutral (q : Class S K (finiteC Γ) τ) : ClassNonLambda q →
    (∀ r, ClassEdge q r → ComputableClass S K Γ hk τ r) → ComputableClass S K Γ hk τ q
  bottom (q : Class S K (finiteC Γ) τ) : ClassBottom q → ComputableClass S K Γ hk τ q
  variableCase (q : Class S K (finiteC Γ) τ) : VariableClass q → ComputableClass S K Γ hk τ q
  accessible (q : Class S K (finiteC Γ) τ) : ComputableClass S K Γ hk τ q →
    Acc (fun r q => RS S K (finiteC Γ) τ q r) q

private theorem withAtoms {S K Γ hk τ}
    (neutral : ∀ q : Class S K (finiteC Γ) τ, ClassNonLambda q →
      (∀ r, ClassEdge q r → ComputableClass S K Γ hk τ r) → ComputableClass S K Γ hk τ q)
    (accessible : ∀ q : Class S K (finiteC Γ) τ, ComputableClass S K Γ hk τ q →
      Acc (fun r q => RS S K (finiteC Γ) τ q r) q) : Facts S K Γ hk τ := by
  have hb : ∀ q : Class S K (finiteC Γ) τ, ClassBottom q → ComputableClass S K Γ hk τ q :=
    fun q h => neutral q (bottomNeutral h) (fun _ s => (bottomNoEdge h s).elim)
  exact ⟨neutral,hb,fun q h => neutral q (variableNeutral h) (fun r s => hb r (variableEdge h s)),accessible⟩

private theorem variableFor {S K Γ σ τ} (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K (finiteC Γ) (.arrow σ τ)) :
    ∃ u : Class S K (finiteC Γ) σ, VariableClass u := by
  induction q using Quot.ind with
  | _ Q =>
    let i := (NumberedWindowPrimaryCoverSyntax.termBounds Q.val).numeral + 1
    have inside := NumberedWindowApplicationDomainProof.rootInWindow Q.property
    let U : WindowCarrier S K (finiteC Γ) σ :=
      ⟨.free σ i, .free, NumberedWindowApplicationDomainProof.arrowLeft hk inside,
        by intro f hf; cases hf⟩
    exact ⟨classOf U, U, ⟨i,Or.inl rfl⟩, rfl⟩

private theorem facts (S : Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K) (τ : Ty) :
    Facts S K Γ hk τ := by
  induction τ with
  | ground =>
    apply withAtoms (accessible := fun q => (groundAcc hk q).mp)
    intro q _ reducts
    apply (groundAcc hk q).mpr
    constructor
    intro r path
    cases path with
    | one edge => exact (groundAcc hk r).mp (reducts r edge)
    | more edge tail => exact ((groundAcc hk _).mp (reducts _ edge)).inv tail
  | arrow σ τ domain codomain =>
    apply withAtoms
    · intro q nonLambda reducts u hu
      apply codomain.neutral (appClass hk q u) (exact_NonLambdaApplicationClass S K (finiteC Γ) σ τ hk q u)
      intro out step
      rcases exact_NeutralApplicationEdges S K (finiteC Γ) σ τ hk q u out nonLambda step with
        hb | ⟨next,hn,rfl⟩
      · exact codomain.bottom out hb
      · exact reducts next hn u hu
    · intro q hq
      obtain ⟨u,hu⟩ := variableFor hk q
      have acc := codomain.accessible (appClass hk q u) (hq u (domain.variableCase u hu))
      obtain ⟨i,hi⟩ := (exact_ActualClassCodeFibers S K Γ (.arrow σ τ) hk).1 q
      obtain ⟨j,hj⟩ := (exact_ActualClassCodeFibers S K Γ τ hk).1 (appClass hk q u)
      apply (exact_ScalarClassAccessibility S K Γ (.arrow σ τ) hk q i hi).mp
      exact exact_ExternalIApplicationPullback S K Γ σ τ hk q u i j hi hj
        ((exact_ScalarClassAccessibility S K Γ τ hk (appClass hk q u) j hj).mpr acc)

theorem neutral : NeutralComputability := fun S K Γ τ hk => (facts S K Γ hk τ).neutral
theorem bottom : BottomComputability := fun S K Γ τ hk => (facts S K Γ hk τ).bottom
theorem variableCase : VariableComputability := fun S K Γ τ hk => (facts S K Γ hk τ).variableCase
theorem scalarI : ComputabilityImpliesScalarI := by
  intro S K Γ τ hk q i hi hq
  exact (exact_ScalarClassAccessibility S K Γ τ hk q i hi).mpr ((facts S K Γ hk τ).accessible q hq)

end LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsProof
