module
public import LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation StructuralRenaming

def LiteralErasure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (τ : Ty) (r : Renaming Γ Δ) (q : ConfinedTerm I Γ τ) , (renameSource r q).val=Source.SourceMarkedBinding.renameTerm q.val r

def InterpretationCovariance : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (τ : Ty) (r : Renaming Γ Δ) (q : ConfinedTerm I Γ τ) (M : Constructors I) (P : World I) (ρ : Environment I Δ P),interpret (renameSource r q) M P ρ=interpret q M P (reindex r ρ)

def ScannerCovariance : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (τ : Ty) (r : Renaming Γ Δ) (q : ConfinedTerm I Γ τ) (M : Constructors I) (P : World I) (ρ : Environment I Δ P) (mask : Protected Δ) (types : List Ty) (υ : Ty) (args : Values I types P) (h : τ=arrows types υ),scan (renameSource r q) M P ρ mask types υ args h=scan q M P (reindex r ρ) (pullMask r mask) types υ args h

end LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingTargets
