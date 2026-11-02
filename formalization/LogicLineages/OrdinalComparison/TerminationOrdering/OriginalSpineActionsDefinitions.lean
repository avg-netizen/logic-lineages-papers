module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActions
open Source Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice

abbrev Protected (Γ : List Ty) := {τ : Ty} → Variable Γ τ → Bool

abbrev Evaluate {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) :=
  Constructors I → (P : World I) → Environment I Γ P → Value I σ P
abbrev Scan {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) :=
  Constructors I → (P : World I) → Environment I Γ P → Protected Γ →
    (types : List Ty) → (τ : Ty) → Values I types P → σ=arrows types τ → Value I τ P

def EvaluationMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {σ : Ty}
    (e : Evaluate I Γ σ) : Prop := ∀ M N P (ρ η : Environment I Γ P),M ≤ N → EnvLE ρ η → e M P ρ ≤ e N P η

def EvaluationNatural {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {σ : Ty}
    (e : Evaluate I Γ σ) : Prop := ∀ M P Q (h : Extends P Q) (ρ : Environment I Γ P),
      RecursiveNaturalDomains.weaken h (e M P ρ)=e M Q (restrict h ρ)

def ScanMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {σ : Ty}
    (s : Scan I Γ σ) : Prop := ∀ M N P (ρ η : Environment I Γ P) (mask : Protected Γ)
      types τ (v w : Values I types P) (h : σ=arrows types τ),M ≤ N → EnvLE ρ η → v ≤ w →
        s M P ρ mask types τ v h ≤ s N P η mask types τ w h

def ScanNatural {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {σ : Ty}
    (s : Scan I Γ σ) : Prop := ∀ M P Q (hPQ : Extends P Q) (ρ : Environment I Γ P) (mask : Protected Γ)
      types τ (v : Values I types P) (h : σ=arrows types τ),
      RecursiveNaturalDomains.weaken hPQ (s M P ρ mask types τ v h)=
        s M Q (restrict hPQ ρ) mask types τ (weakenValues hPQ v) h

/-- Certificates are induction obligations; only explicit constructed actions will be used. -/
structure PairedAction {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) where
  evaluate : Evaluate I Γ σ
  scan : Scan I Γ σ
  evaluateMonotone : EvaluationMonotone evaluate
  evaluateNatural : EvaluationNatural evaluate
  scanMonotone : ScanMonotone scan
  scanNatural : ScanNatural scan
  scanEmpty : ∀ M P (ρ : Environment I Γ P) (mask : Protected Γ) (v : Values I [] P),
    scan M P ρ mask [] σ v rfl=evaluate M P ρ

def variableEvaluate {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {σ : Ty}
    (v : Variable Γ σ) : Evaluate I Γ σ := fun _ _ ρ => ρ v

def variableScan {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {σ : Ty}
    (v : Variable Γ σ) : Scan I Γ σ := fun _ P ρ mask types τ args h =>
  if types=[] then applyWith (ρ v) types τ args h
  else if mask v then ExecutableDomainBottom.bottomValue I τ P
  else applyWith (ρ v) types τ args h

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActions
