import LogicLineages.PersistentMarking.NumberedWindowStructuralLambdaProof
import LogicLineages.PersistentMarking.NumberedWindowConstructorComputabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowTupleBridgeProof

namespace LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowArithmeticLeastClass
open NumberedWindowSimulationData NumberedWindowExternalComputability NumberedWindowExternalApplication
open NumberedWindowStructuralComputabilityTargets NumberedWindowConstructorComputabilityTargets
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorComputabilityChecks
open NumberedWindowPreservationGuardProof NumberedWindowNumberedDomainProof

private theorem asArgument {S K Γ hk τ q} (h : TypedComputable S K Γ hk τ q) :
    ComputableArgument S K Γ hk q := by
  obtain ⟨hw,hc⟩ := h
  unfold ComputableArgument
  rw [NumberedWindowApplicationDomainProof.annotation hw.1]
  exact ⟨hw,hc⟩

private def TermClaim (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K) (q : NTerm) : Prop :=
  ∀ C τ, InWindow S K C τ q → ∀ values, Environment S K Γ hk C values →
    TypedComputable S K Γ hk τ (substitute values 0 q)

private def ArgsClaim (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K) (xs : NArgs) : Prop :=
  ∀ C, ExtrasTyped C xs → ArgsGuard S K xs → ∀ values, Environment S K Γ hk C values →
    Members S K Γ hk (substituteArgs values 0 xs)

private theorem structural (S K Γ) (hk : DecisionSourceUniverse.Closed K) (q : NTerm) : TermClaim S K Γ hk q := by
  induction q using NTerm.rec (motive_2 := ArgsClaim S K Γ hk) with
  | free σ i =>
    intro C τ hw vs env
    cases hw.1 with
    | free =>
      have image : InWindow S K (finiteC Γ) σ (.free σ i) := ⟨.free,hw.2⟩
      exact ⟨image,NumberedWindowExternalTypeFactsChecks.exact_VariableComputability S K Γ σ hk _
        ⟨⟨_,image⟩,⟨i,Or.inl rfl⟩,rfl⟩⟩
  | bound σ i =>
    intro C τ hw vs env
    cases hw.1 with
    | bound hi => exact env _ _ hi (NumberedWindowApplicationDomainProof.rootInWindow hw)
  | bottom σ =>
    intro C τ hw vs env
    cases hw.1 with
    | bottom =>
      have image : InWindow S K (finiteC Γ) σ (.bottom σ) := ⟨.bottom,hw.2⟩
      exact NumberedWindowConstructorContextCasesProof.bottom image
  | lam σ body ih =>
    intro C ρ hw values env
    cases hw.1 with
    | lam =>
      exact NumberedWindowStructuralLambdaProof.lambda hk values hw env
        (fun vals compatible => ih _ _ (lamBody hw) vals compatible)
  | ordinary f bs ib =>
    intro C τ hw vs env
    cases hw.1 with
    | ordinary hb =>
      obtain ⟨_,_,guard⟩ := ordinaryParts hw
      have image := NumberedWindowPreservationSubstitutionProof.term S K hk vs 0 C _ _ _ hw
        (NumberedWindowStructuralEnvironmentProof.compatible env)
      exact exact_AllConstructorsComputable S K Γ hk (.ordinary f (substituteArgs vs 0 bs)) image
        (ib C (toExtras hb) guard vs env) NumberedWindowConstructorContextCasesProof.emptyMembers
  | numbered f τ k bs es ib ie =>
    intro C ρ hw vs env
    cases hw.1 with
    | numbered hb he =>
      obtain ⟨_,_,_,gb,ge⟩ := parts hw
      have image := NumberedWindowPreservationSubstitutionProof.term S K hk vs 0 C _ _ _ hw
        (NumberedWindowStructuralEnvironmentProof.compatible env)
      exact exact_AllConstructorsComputable S K Γ hk (.numbered f τ k (substituteArgs vs 0 bs) (substituteArgs vs 0 es))
        image (ib C (toExtras hb) gb vs env) (ie C he ge vs env)
  | auxApp σ τ q u iq iu =>
    intro C ρ hw vs env
    cases hw.1 with
    | auxApp =>
      obtain ⟨qw,uw⟩ := appParts hw
      obtain ⟨fq,hf⟩ := iq C _ qw vs env
      obtain ⟨aq,ha⟩ := iu C _ uw vs env
      let f : WindowCarrier S K (finiteC Γ) (.arrow σ τ) := ⟨substitute vs 0 q,fq⟩
      let a : WindowCarrier S K (finiteC Γ) σ := ⟨substitute vs 0 u,aq⟩
      exact ⟨(appCarrier hk f a).property,hf (classOf a) ha⟩
  | nil => intros; exact NumberedWindowConstructorContextCasesProof.emptyMembers
  | cons q xs iq ix =>
    intro C ht hg vs env
    cases ht with
    | cons tq ts =>
      obtain ⟨g,gs⟩ := consParts hg
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact asArgument (iq C _ ⟨tq,g⟩ vs env)
      · exact ix C ts gs vs env r hr

theorem substitution : StructuralComputableSubstitution :=
  fun S K Γ hk C values τ q hw env => structural S K Γ hk q C τ hw values env

private theorem identityEnvironment (S K Γ) (hk : DecisionSourceUniverse.Closed K) :
    Environment S K Γ hk (finiteC Γ) .nil := by
  intro i τ lookup member
  rw [NumberedWindowTupleBridgeProof.emptySubstitute]
  have hw : InWindow S K (finiteC Γ) τ (.bound τ i) :=
    ⟨.bound lookup,hk τ member,fun _ h => nomatch h⟩
  exact ⟨hw,NumberedWindowExternalTypeFactsChecks.exact_VariableComputability S K Γ τ hk _
    ⟨⟨_,hw⟩,⟨i,Or.inr rfl⟩,rfl⟩⟩

theorem everyTerm : EveryAdmittedTermComputable := by
  intro S K Γ hk τ q hw
  simpa only [NumberedWindowTupleBridgeProof.emptySubstitute] using
    structural S K Γ hk q (finiteC Γ) τ hw .nil (identityEnvironment S K Γ hk)

theorem everyAddress : EveryActualAddressInExternalI := by
  intro S K Γ τ hk x i hx
  obtain ⟨q,rfl,hcode⟩ := hx
  obtain ⟨_,hc⟩ := everyTerm S K Γ hk τ q.val q.property
  exact NumberedWindowExternalTypeFactsChecks.exact_ComputabilityImpliesScalarI S K Γ τ hk (classOf q) i
    ⟨q,rfl,hcode⟩ hc

end LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityProof
