module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActionsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActions
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions TypedExtraDownsets FullTuplePacking OrdinaryFunctionalValue

abbrev ArgumentActions {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (Γ types : List Ty) := (i : Fin types.length) → PairedAction I Γ (types.get i)

def evaluateArguments {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ types : List Ty} (A : ArgumentActions I Γ types) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) : Values I types P :=
  fun i => (A i).evaluate M P ρ

def packArguments {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (types : List Ty) (ht : ∀ τ ∈ types,τ ∈ TypedExtraDownsets.types I) {P : World I}
    (v : Values I types P) : List (TypedExtraDownsets.Packed I P) :=
  List.ofFn fun i => ⟨⟨types.get i,ht _ (List.get_mem _ _)⟩,v i⟩

def markedState {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) : Inputs I f P :=
  ⟨evaluateArguments base M P ρ,
    TypedExtraAppendProof.appendExtras (emptyExtras I P) (packArguments extraTypes ht (evaluateArguments extras M P ρ))⟩

def ordinaryState {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) : Inputs I f P :=
  ⟨evaluateArguments base M P ρ,emptyExtras I P⟩

def sourceSuffix {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity}
    (σ : TypeIndex I) (types : List Ty) (τ : Ty) (h : σ.val=arrows types τ) (hne : types ≠ []) : Suffix σ.val :=
  ⟨(types,τ),(Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration σ.val types τ).mpr ⟨hne,h.symm⟩⟩

/-- A helper with explicit data arguments, not an assumed semantic action. -/
def functionalScan {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (e : Evaluate I Γ σ.val)
    (state : (M : Constructors I) → (P : World I) → Environment I Γ P → Inputs I f P) : Scan I Γ σ.val :=
  fun M P ρ _ types τ args h =>
    if hn : types=[] then Eq.mp (congrArg (fun υ => Value I υ P) (by simpa [hn,arrows] using h)) (e M P ρ)
    else M.val f (resultTag I σ (sourceSuffix σ types τ h hn)) P
      (FunctionalTupleBuilder.appendInput (state M P ρ) (packTuple σ (sourceSuffix σ types τ h hn) args))

def markedEvaluate {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) : Evaluate I Γ σ.val :=
  fun M P ρ => M.val f σ P (markedState f base extraTypes ht extras M P ρ)

def markedScan {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) : Scan I Γ σ.val :=
  functionalScan f σ (markedEvaluate f σ base extraTypes ht extras) (markedState f base extraTypes ht extras)

def ordinaryEvaluate {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) : Evaluate I Γ (headResult f.val) :=
  fun M P ρ => ordinaryValue M f (evaluateArguments base M P ρ)

def ordinaryScan {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) : Scan I Γ (headResult f.val) :=
  functionalScan f ⟨headResult f.val,OrdinaryFunctionalValueProof.sourceHeadResultTypes Symbol inferInstance arity I f⟩
    (ordinaryEvaluate f base) (ordinaryState f base)

end LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActions
