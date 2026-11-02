module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupportTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution ComparisonFreeVariables SubstitutionEnvironmentSupport LambdaSpineActions

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem supportedMono {Γ : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ)
    (a b : Allowed Γ) (ha : Supported q a) (h : ∀ {υ} (v : Variable Γ υ),a v → b v) : Supported q b := by
  apply (ComparisonFreeVariablesSyntaxProof.supportCalibration Symbol arity Γ τ q b).mpr
  intro v hv
  exact h v.2 ((ComparisonFreeVariablesSyntaxProof.supportCalibration Symbol arity Γ τ q a).mp ha v hv)

theorem liftMaskSupport {Γ : List Ty} {σ τ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) τ)
    (mask mask' : Protected Γ) (h : Supported body (liftAllowed (fun {_} v => mask v=mask' v))) :
    Supported body (fun {_} v => protectExtend mask v=protectExtend mask' v) := by
  apply supportedMono body _ _ h
  intro υ v hv
  cases v with
  | here => rfl
  | there v => exact hv

theorem scannerMask {Γ : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ) :
    ∀ (hq : Confined I q) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (mask mask' : Protected Γ),
      Supported q (fun {_} v => mask v=mask' v) →
      ∀ types υ (args : Values I types P) (h : τ=arrows types υ),
        (buildTerm I q hq).scan M P ρ mask types υ args h=(buildTerm I q hq).scan M P ρ mask' types υ args h := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro hq M P ρ mask mask' hs types υ args h
    change mask v=mask' v at hs
    change variableScan v M P ρ mask types υ args h=variableScan v M P ρ mask' types υ args h
    simp only [variableScan,hs]
  | lam body ih =>
    intro hq M P ρ mask mask' hs types υ args h
    change lambdaScan (buildTerm I body ⟨hq.1.2.2,hq.2⟩) _ M P ρ mask types υ args h=
      lambdaScan (buildTerm I body ⟨hq.1.2.2,hq.2⟩) _ M P ρ mask' types υ args h
    by_cases hn : types=[]
    · simp only [lambdaScan,dif_pos hn]
    · cases types with
      | nil => exact False.elim (hn rfl)
      | cons α rest =>
        simp only [lambdaScan,dif_neg hn,consumeNonempty,consume]
        exact ih ⟨hq.1.2.2,hq.2⟩ M P _ _ _ (liftMaskSupport body mask mask' hs)
          rest υ (tailValues args) (Ty.arrow.inj h).2
  | ordinary f base ih =>
    intro hq M P ρ mask mask' hs types υ args h
    rfl
  | marked f output base ts extras ihb ihe =>
    intro hq M P ρ mask mask' hs types υ args h
    rfl
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem maskLocality : SubstitutionEnvironmentSupportTargets.MaskLocality := by
  intro Symbol inst arity I Γ τ q M P ρ mask mask' hs types υ args h
  exact scannerMask q.val q.property M P ρ mask mask' hs types υ args h

theorem agreementRestriction : SubstitutionEnvironmentSupportTargets.AgreementRestriction := by
  intro Symbol inst arity I Γ Δ M s hs P Q h ρ η ha τ v ht
  exact (congrArg (RecursiveNaturalDomains.weaken h) (ha v ht)).trans
    ((action (⟨s v,hs v ht⟩ : ConfinedTerm I Δ τ)).evaluateNatural M P Q h η)

theorem agreementLift : SubstitutionEnvironmentSupportTargets.AgreementLift := by
  intro Symbol inst arity I Γ Δ σ M s hs P a ρ η ha τ v ht
  cases v with
  | here => rfl
  | there v =>
    exact (ha v ht).trans (StructuralRenamingProof.interpretationCovariance Symbol inst arity I Δ (σ::Δ) τ
      (Renaming.weaken Δ σ) ⟨s v,hs v ht⟩ M P (extend a η)).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupportProof
