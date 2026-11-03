module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationSupportProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions TypedExtraDownsets FullTuplePacking OrdinaryFunctionalValue ConfinedStructuralInterpretation SourceConstructorIteration

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

def suffixOf (σ : Ty) (types : List Ty) (τ : Ty) (h : σ=arrows types τ) (hn : types≠[]) : Suffix σ :=
  ⟨(types,τ),(Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration σ types τ).mpr ⟨hn,h.symm⟩⟩

theorem withSuffix {P : World I} {σ : Ty} (a : Value I σ P) (types : List Ty) (τ : Ty)
    (args : Values I types P) (h : σ=arrows types τ) (hn : types≠[]) :
    applyWith a types τ args h=applyValue a (suffixOf σ types τ h hn) args := by
  cases h
  cases types with
  | nil => exact False.elim (hn rfl)
  | cons α rest => rfl

theorem emptyApplication {Γ : List Ty} {σ : Ty} (A : PairedAction I Γ σ) (M : Constructors I) (P : World I)
    (ρ : Environment I Γ P) (mask : Protected Γ) (types : List Ty) (τ : Ty) (args : Values I types P)
    (h : σ=arrows types τ) (hn : types=[]) :
    applyWith (A.evaluate M P ρ) types τ args h=A.scan M P ρ mask types τ args h := by
  subst types
  cases h
  exact (A.scanEmpty M P ρ mask args).symm

theorem limitCurrentTuple (above : Symbol → Symbol → Prop) [DecidableRel above]
    (f : HeadIndex I) (σ : TypeIndex I) (P : World I) (a : Inputs I f P)
    (s : Suffix σ.val) (args : FullTuple I σ.val s P) :
    applyValue ((limit I above).val f σ P a) s args =
      (limit I above).val f (resultTag I σ s) P (FunctionalTupleBuilder.appendInput a (packTuple σ s args)) := by
  exact (ActualLimitInterpretationProof.fullTupleEquation Symbol inferInstance arity I above inferInstance
    f σ P a ⟨P,fun _ hp => hp⟩ s args).trans
    (congrArg ((limit I above).val f (resultTag I σ s) P)
      (congrArg (fun x => FunctionalTupleBuilder.appendInput x (packTuple σ s args)) ((inputFamily I f).restrictIdentity P a)))

theorem lambdaApplication {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ)
    (A : PairedAction I (σ::Γ) υ) (M : Constructors I) (P : World I) (ρ : Environment I Γ P)
    (types : List Ty) (τ : Ty) (args : Values I types P) (h : Ty.arrow σ υ=arrows types τ) (hn : types≠[]) :
    applyWith ((LambdaSpineActionsProof.lambdaAction body A).evaluate M P ρ) types τ args h=
      (LambdaSpineActionsProof.lambdaAction body A).scan M P ρ (fun {_} _ => false) types τ args h := by
  rw [withSuffix _ types τ args h hn]
  change applyValue (LambdaSpineActionsProof.lambdaValue body A M P ρ) (suffixOf (.arrow σ υ) types τ h hn) args = _
  simp only [LambdaSpineActionsProof.lambdaAction,LambdaSpineActions.lambdaScan,dif_neg hn]
  let s := suffixOf (.arrow σ υ) types τ h hn
  have hv := congrArg (fun raw : NaturalTupleLayer.Raw I (.arrow σ υ) (lower I (.arrow σ υ)) P =>
      raw.2 ⟨P,fun _ hp => hp⟩ s args) (LambdaSpineActionsProof.valueLayer body A M P ρ)
  exact hv.trans (congrArg (fun env : Environment I Γ P =>
    LambdaSpineActions.consumeNonempty A M P env (fun {_} _ => false) types τ args h hn)
    (TypedValueEnvironmentProof.restrictionIdentity Symbol inferInstance arity I Γ P ρ))

theorem ordinaryApplication {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (types : List Ty) (τ : Ty)
    (args : Values I types P) (h : headResult f.val=arrows types τ) (hn : types≠[]) :
    applyWith ((FunctionalSpineActionsProof.ordinaryAction f base).evaluate M P ρ) types τ args h=
      (FunctionalSpineActionsProof.ordinaryAction f base).scan M P ρ (fun {_} _ => false) types τ args h := by
  rw [withSuffix _ types τ args h hn]
  simp only [FunctionalSpineActionsProof.ordinaryAction,FunctionalSpineActionsProof.assembleAction,
    functionalScan,dif_neg hn]
  let b := evaluateArguments base M P ρ
  let s := suffixOf (headResult f.val) types τ h hn
  obtain ⟨hr,he⟩ := OrdinaryFunctionalValueProof.fullTupleEquation Symbol inferInstance arity I M f P b
  have hb : weakenBase (fun _ hp => hp) b=b := by
    funext i
    exact (family I _).restrictIdentity P (b i)
  have hv := he ⟨P,fun _ hp => hp⟩ s args
  have heq := congrArg (fun c : BaseTuple I f P => M.val f (resultTag I ⟨headResult f.val,hr⟩ s) P
    ⟨c,TypedExtraAppendProof.appendExtras (emptyExtras I P) (packTuple ⟨headResult f.val,hr⟩ s args)⟩) hb
  exact hv.trans heq

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationSupportProof
