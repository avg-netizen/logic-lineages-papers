module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxLambdaBitsProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains
open TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation OriginalSpineActions
open RelatedEnvironments ActualValueLogicalRelation ActualComparisonCompleteness TypedObservationAccess RecursiveComparison
open RelationalSyntax RelationalSyntaxSupportProof LambdaSpineActions LambdaObservationMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem futureSubstitute {Gamma : List Ty} {sigma : Ty} (q : MarkedTerm Symbol arity Gamma sigma)
    {P Q : World I} (h : Extends P Q)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context)) :
    futureSyntax h (substituteTerm q s)=substituteTerm q (futureSubstitution h s) := by
  have H := RenamingEquivarianceBindingProof.substitutionCovariance Symbol arity
    Gamma Gamma (portTypes P.val++I.context) (portTypes Q.val++I.context) sigma q
    (fun v => v) (LogicalRelationWorlds.portRename h) s (futureSubstitution h s) (by intros; rfl)
  rw [SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Gamma sigma q] at H
  exact H.symm

theorem lambdaRead {Gamma : List Ty} {sigma upsilon : Ty}
    (body : ConfinedTerm I (sigma::Gamma) upsilon) (M : Constructors I) (P : World I)
    (rho : Environment I Gamma P) (strict : Bool)
    (target : Term Symbol arity (portTypes P.val++I.context) (.arrow sigma upsilon))
    (ho : (⟨P.val,.arrow sigma upsilon,target⟩ : Observation Symbol arity I.context (budget I)) ∈
      observations (budget I) I.target) :
    readBit strict (LambdaSpineActionsProof.lambdaValue body.val (action body) M P rho)
      ⟨P.val,.arrow sigma upsilon,target⟩=
      matchTerm strict (bodyEvaluator body.val (action body) M) rho target := by
  let o : ObservationAt I (.arrow sigma upsilon) P := ⟨⟨P.val,.arrow sigma upsilon,target⟩,ho,rfl,rfl⟩
  rw [TypedObservationAccessProof.typedCoordinate Symbol inferInstance arity I _ P strict _ ⟨P,fun _ hp => hp⟩ o]
  cases strict with
  | false =>
    simp only [coordinate,Bool.false_eq_true,↓reduceIte,LambdaSpineActionsProof.valueLayer]
    change matchTerm false (bodyEvaluator body.val (action body) M) (restrict (fun _ hp => hp) rho) target=_
    rw [TypedValueEnvironmentProof.restrictionIdentity Symbol inferInstance arity I Gamma P rho]
  | true =>
    simp only [coordinate,↓reduceIte,LambdaSpineActionsProof.valueLayer]
    change matchTerm true (bodyEvaluator body.val (action body) M) (restrict (fun _ hp => hp) rho) target=_
    rw [TypedValueEnvironmentProof.restrictionIdentity Symbol inferInstance arity I Gamma P rho]

/-- A local genuine-body induction step. The final joint theorem must pay its
EvaluationRelated premise by actual syntax induction, not take it as an oracle. -/
theorem currentSound (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma upsilon : Ty} (body : ConfinedTerm I (sigma::Gamma) upsilon)
    (he : EvaluationRelated I above M body) (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
    (hr : EnvironmentRelated I above P rho s) (strict : Bool) (o : ObservationAt I (.arrow sigma upsilon) P)
    (hb : readBit strict (LambdaSpineActionsProof.lambdaValue body.val (action body) M P rho) o.val=true) :
    if strict then Strict Symbol arity above (portTypes P.val++I.context)
      ⟨.arrow sigma upsilon,substituteTerm (.lam body.val) s⟩ ⟨.arrow sigma upsilon,observedTerm o⟩
    else Weak Symbol arity above (portTypes P.val++I.context)
      ⟨.arrow sigma upsilon,substituteTerm (.lam body.val) s⟩ ⟨.arrow sigma upsilon,observedTerm o⟩ := by
  rcases o with ⟨⟨ports,tau,target⟩,hom,hports,htype⟩
  dsimp at hports htype
  subst ports
  subst tau
  rw [lambdaRead body M P rho strict target hom] at hb
  cases target <;> try (simp only [matchTerm,Bool.false_eq_true] at hb)
  case lam target =>
    obtain ⟨i,hopen,hread⟩ := (LambdaObservationMatchingProof.literalMatch Symbol inferInstance arity I Gamma
      sigma upsilon body.val (bodyEvaluator body.val (action body) M) P rho strict target).mp hb
    have hobs := (MarkedFAbsTestProof.genuineOpeningGuards Symbol inferInstance arity I P sigma upsilon target i hom hopen.1).2
    let Q : World I := ⟨(i,sigma)::P.val,hopen.2.1⟩
    have henv : EnvironmentRelated I above Q (openingEnvironment rho sigma upsilon i hopen) (liftSubstitution s) :=
      RelatedEnvironmentsProof.freshOpening Symbol inferInstance arity I above Gamma P rho s
        sigma upsilon i hopen hr
    have hbody := he Q (openingEnvironment rho sigma upsilon i hopen) (liftSubstitution s) henv
    let obody : ObservationAt I upsilon Q := ⟨⟨Q.val,upsilon,target⟩,hobs,rfl,rfl⟩
    have hbits := currentBits above _ _ hbody obody
    change readBit strict (interpret body M Q (openingEnvironment rho sigma upsilon i hopen)) obody.val=true at hread
    cases strict with
    | false =>
      exact Weak.abs _ _ (hbits.1 hread)
    | true =>
      exact LiteralContextsProof.lambdaStrictCongruence Symbol arity above (portTypes P.val++I.context)
        sigma upsilon _ _ (hbits.2 hread)

theorem bitSound (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma upsilon : Ty} (body : ConfinedTerm I (sigma::Gamma) upsilon)
    (he : EvaluationRelated I above M body) (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
    (hr : EnvironmentRelated I above P rho s) :
    BitSound I above (.arrow sigma upsilon) P
      (LambdaSpineActionsProof.lambdaValue body.val (action body) M P rho) (substituteTerm (.lam body.val) s) := by
  intro Q h o
  have hv := LambdaSpineActionsProof.valueNatural body.val (action body) M P Q h rho
  have henv : EnvironmentRelated I above Q (restrict h rho) (futureSubstitution h s) :=
    RelatedEnvironmentsProof.weakening Symbol inferInstance arity I above Gamma P Q h rho s hr
  rw [futureSubstitute (.lam body.val) h s]
  constructor
  · intro hb
    rw [hv] at hb
    exact currentSound above M body he Q (restrict h rho) (futureSubstitution h s) henv false o hb
  · intro hb
    rw [hv] at hb
    exact currentSound above M body he Q (restrict h rho) (futureSubstitution h s) henv true o hb

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxLambdaBitsProof
