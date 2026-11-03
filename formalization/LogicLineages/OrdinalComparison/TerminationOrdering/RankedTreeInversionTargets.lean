module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeInversionTargets
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree

def GroundArgumentInjectivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (n : Nat) (f g : Fin n → MarkedTerm Symbol arity Gamma .ground),
    groundArguments n f=groundArguments n g → ∀ i,f i=g i

def EmbeddingInjectivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty),
    Function.Injective (pack (Symbol := Symbol) (arity := arity) (Gamma := Gamma))

def OrdinaryRootEquality : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (g : Symbol) (args : Fin (arity g) → Tree Symbol arity Gamma),
  (⟨headResult f,.ordinary f base⟩ : Packed Symbol arity Gamma)=pack (.node g args) →
    f=.ranked g ∧ HEq base (groundArguments (arity g) (fun i => markedSyntax (args i)))

def MarkedRootEquality : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (g : Symbol) (args : Fin (arity g) → Tree Symbol arity Gamma),
  (⟨tau,.marked f tau base types extras⟩ : Packed Symbol arity Gamma)=markedRoot g args →
    f=.ranked g ∧ tau=.ground ∧ types=[] ∧
    HEq base (groundArguments (arity g) (fun i => markedSyntax (args i))) ∧
    HEq extras (Arguments.nil : Arguments Symbol arity Gamma [])

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeInversionTargets
