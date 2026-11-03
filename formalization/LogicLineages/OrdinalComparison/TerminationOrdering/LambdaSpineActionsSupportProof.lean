module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsSupportProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions LambdaObservationMatching LambdaSpineActions

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem binderProtection : LambdaSpineActionsTargets.BinderProtection := by
  intro Γ σ mask
  exact ⟨rfl,fun {_} _ => rfl⟩
theorem binderConsumption : LambdaSpineActionsTargets.BinderConsumption := by
  intro Symbol inst arity I Γ σ υ A M P ρ mask α rest τ args h
  rfl

theorem castMonotone {P : World I} {σ τ : Ty} (h : σ=τ) {a b : Value I σ P} (hab : a ≤ b) : castValue h a ≤ castValue h b := by
  cases h
  exact hab

theorem castNatural {P Q : World I} (hPQ : Extends P Q) {σ τ : Ty} (h : σ=τ) (a : Value I σ P) :
    RecursiveNaturalDomains.weaken hPQ (castValue h a)=castValue h (RecursiveNaturalDomains.weaken hPQ a) := by
  cases h
  rfl

theorem consumeMonotone {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ)
    {M N : Constructors I} {P : World I} {ρ η : Environment I Γ P} (hMN : M ≤ N) (hρη : EnvLE ρ η)
    (mask : Protected Γ) (α : Ty) (rest : List Ty) (τ : Ty) (args args' : Values I (α::rest) P)
    (h : Ty.arrow σ υ=arrows (α::rest) τ) (ha : args ≤ args') :
    consume A M P ρ mask α rest τ args h ≤ consume A N P η mask α rest τ args' h := by
  apply A.scanMonotone M N P _ _ _ rest τ _ _ _ hMN
  · exact TypedValueEnvironmentProof.extensionMonotone Symbol inferInstance arity I Γ σ P _ _ ρ η
      (castMonotone _ (ha ⟨0,by simp⟩)) hρη
  · intro i
    exact ha i.succ

theorem consumeNatural {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) {P Q : World I} (hPQ : Extends P Q) (ρ : Environment I Γ P)
    (mask : Protected Γ) (α : Ty) (rest : List Ty) (τ : Ty) (args : Values I (α::rest) P)
    (h : Ty.arrow σ υ=arrows (α::rest) τ) :
    RecursiveNaturalDomains.weaken hPQ (consume A M P ρ mask α rest τ args h)=
      consume A M Q (restrict hPQ ρ) mask α rest τ (weakenValues hPQ args) h := by
  let first := castValue (Ty.arrow.inj h).1.symm (args ⟨0,by simp⟩)
  have henv : @Eq (Environment I (σ::Γ) Q)
      (restrict hPQ (extend first ρ))
      (extend (castValue (Ty.arrow.inj h).1.symm ((weakenValues hPQ args) ⟨0,by simp⟩)) (restrict hPQ ρ)) := by
    funext β v
    cases v with
    | here => exact castNatural hPQ (Ty.arrow.inj h).1.symm (args ⟨0,by simp⟩)
    | there v => rfl
  exact (A.scanNatural M P Q hPQ (extend first ρ) (protectExtend mask) rest τ (tailValues args) (Ty.arrow.inj h).2).trans
    (congrArg (fun env : Environment I (σ::Γ) Q => A.scan M Q env (protectExtend mask) rest τ
      (tailValues (weakenValues hPQ args)) (Ty.arrow.inj h).2) henv)

theorem nonemptyMonotone {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ)
    {M N : Constructors I} {P : World I} {ρ η : Environment I Γ P} (hMN : M ≤ N) (hρη : EnvLE ρ η)
    (mask : Protected Γ) (types : List Ty) (τ : Ty) (args args' : Values I types P)
    (h : Ty.arrow σ υ=arrows types τ) (hn : types≠[]) (ha : args ≤ args') :
    consumeNonempty A M P ρ mask types τ args h hn ≤ consumeNonempty A N P η mask types τ args' h hn := by
  cases types with
  | nil => exact False.elim (hn rfl)
  | cons α rest => exact consumeMonotone A hMN hρη mask α rest τ args args' h ha

theorem nonemptyNatural {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) {P Q : World I} (hPQ : Extends P Q) (ρ : Environment I Γ P)
    (mask : Protected Γ) (types : List Ty) (τ : Ty) (args : Values I types P)
    (h : Ty.arrow σ υ=arrows types τ) (hn : types≠[]) :
    RecursiveNaturalDomains.weaken hPQ (consumeNonempty A M P ρ mask types τ args h hn)=
      consumeNonempty A M Q (restrict hPQ ρ) mask types τ (weakenValues hPQ args) h hn := by
  cases types with
  | nil => exact False.elim (hn rfl)
  | cons α rest => exact consumeNatural A M hPQ ρ mask α rest τ args h

end LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsSupportProof
