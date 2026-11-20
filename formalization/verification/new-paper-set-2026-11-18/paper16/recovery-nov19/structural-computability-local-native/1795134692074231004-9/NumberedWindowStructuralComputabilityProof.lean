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

mutual
theorem term (S K Γ) (hk : DecisionSourceUniverse.Closed K) (C : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (hw : InWindow S K C τ q) (values : NArgs) (env : Environment S K Γ hk C values) :
    TypedComputable S K Γ hk τ (substitute values 0 q) := by
  have good := NumberedWindowStructuralEnvironmentProof.compatible env
  have image := NumberedWindowPreservationSubstitutionProof.term S K hk values 0 C _ q τ hw good
  cases hw.1 with
  | free =>
    exact ⟨image,NumberedWindowExternalTypeFactsChecks.exact_VariableComputability S K Γ _ hk _
      ⟨⟨_,image⟩,⟨_,Or.inl rfl⟩,rfl⟩⟩
  | bound hi => exact env _ _ hi (NumberedWindowApplicationDomainProof.rootInWindow hw)
  | bottom =>
    exact ⟨image,NumberedWindowExternalTypeFactsChecks.exact_BottomComputability S K Γ _ hk _
      ⟨⟨_,image⟩,rfl,rfl⟩⟩
  | lam hbody =>
    exact NumberedWindowStructuralLambdaProof.lambda hk values hw env
      (fun vals compatible => term S K Γ hk _ _ _ (lamBody hw) vals compatible)
  | ordinary hb =>
    obtain ⟨_,_,guard⟩ := ordinaryParts hw
    exact exact_AllConstructorsComputable S K Γ hk (.ordinary _ _) image
      (arguments S K Γ hk C _ (toExtras hb) guard values env) NumberedWindowConstructorContextCasesProof.emptyMembers
  | numbered hb he =>
    obtain ⟨_,_,_,gb,ge⟩ := parts hw
    exact exact_AllConstructorsComputable S K Γ hk (.numbered _ _ _ _ _) image
      (arguments S K Γ hk C _ (toExtras hb) gb values env) (arguments S K Γ hk C _ he ge values env)
  | auxApp _ _ =>
    obtain ⟨qW,uW⟩ := appParts hw
    obtain ⟨f,hf⟩ := term S K Γ hk C _ _ qW values env
    obtain ⟨u,hu⟩ := term S K Γ hk C _ _ uW values env
    exact ⟨image,hf (classOf ⟨_,u⟩) hu⟩
termination_by sizeOf q

theorem arguments (S K Γ) (hk : DecisionSourceUniverse.Closed K) (C : Spine.BoundContext) (xs : NArgs)
    (ht : ExtrasTyped C xs) (hg : ArgsGuard S K xs) (values : NArgs) (env : Environment S K Γ hk C values) :
    Members S K Γ hk (substituteArgs values 0 xs) := by
  cases xs with
  | nil => exact NumberedWindowConstructorContextCasesProof.emptyMembers
  | cons q xs =>
    cases ht with
    | cons hq hs =>
      obtain ⟨g,gs⟩ := consParts hg
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact asArgument (term S K Γ hk C q _ ⟨hq,g⟩ values env)
      · exact arguments S K Γ hk C xs hs gs values env r hr
termination_by sizeOf xs
end

theorem substitution : StructuralComputableSubstitution :=
  fun S K Γ hk C values τ q hw env => term S K Γ hk C q τ hw values env

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
    term S K Γ hk (finiteC Γ) q τ hw .nil (identityEnvironment S K Γ hk)

theorem everyAddress : EveryActualAddressInExternalI := by
  intro S K Γ τ hk x i hx
  obtain ⟨q,rfl,hcode⟩ := hx
  obtain ⟨_,hc⟩ := everyTerm S K Γ hk τ q.val q.property
  exact NumberedWindowExternalTypeFactsChecks.exact_ComputabilityImpliesScalarI S K Γ τ hk (classOf q) i
    ⟨q,rfl,hcode⟩ hc

end LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityProof
