module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActions
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions LambdaObservationMatching

def castValue {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I} {σ τ : Ty}
    (h : σ=τ) (a : Value I σ P) : Value I τ P := Eq.mp (congrArg (fun υ => Value I υ P) h) a

def protectExtend {Γ : List Ty} {σ : Ty} (mask : Protected Γ) : Protected (σ::Γ) := fun v => match v with
  | .here => true
  | .there v => mask v

def tailValues {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I} {σ : Ty} {types : List Ty}
    (v : Values I (σ::types) P) : Values I types P := fun i => v i.succ

def consume {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ) (M : Constructors I) (P : World I)
    (ρ : Environment I Γ P) (mask : Protected Γ) (α : Ty) (rest : List Ty) (τ : Ty)
    (args : Values I (α::rest) P) (h : Ty.arrow σ υ=arrows (α::rest) τ) : Value I τ P :=
  A.scan M P (extend (castValue (Ty.arrow.inj h).1.symm (args ⟨0,by simp⟩)) ρ)
    (protectExtend mask) rest τ (tailValues args) (Ty.arrow.inj h).2

def consumeNonempty {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ) (M : Constructors I) (P : World I)
    (ρ : Environment I Γ P) (mask : Protected Γ) :
    (types : List Ty) → (τ : Ty) → Values I types P → Ty.arrow σ υ=arrows types τ → types≠[] → Value I τ P
  | [], _, _, _, hn => False.elim (hn rfl)
  | α::rest, τ, args, h, _ => consume A M P ρ mask α rest τ args h

def bodyEvaluator {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) : BodyEvaluator I body := ⟨fun P ρ => A.evaluate M P ρ⟩

def lambdaRaw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) : NaturalTupleLayer.Raw I (.arrow σ υ) (lower I (.arrow σ υ)) P :=
  ⟨lambdaBits (bodyEvaluator body A M) ρ,fun Q s args =>
    let he := (Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration (.arrow σ υ) s.val.1 s.val.2).mp s.property
    consumeNonempty A M Q.val (restrict Q.property ρ) (fun {_} _ => false) s.val.1 s.val.2 args he.2.symm he.1⟩

def lambdaScan {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ) (e : Evaluate I Γ (.arrow σ υ)) : Scan I Γ (.arrow σ υ) :=
  fun M P ρ mask types τ args h =>
    if hn : types=[] then castValue (by simpa [hn,arrows] using h) (e M P ρ)
    else consumeNonempty A M P ρ mask types τ args h hn

end LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActions
