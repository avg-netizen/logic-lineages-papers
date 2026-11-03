module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedAuxiliaryCoding
def ActualTermCodeInjective : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty),Function.Injective (@termCode Symbol arity Gamma tau)

def ActualArgumentCodeInjective : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty),Function.Injective (@argumentsCode Symbol arity Gamma types)

def ActualPackedCodeInjective : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty),Function.Injective (@packedCode Symbol arity Gamma)

def ActualPackedEquality : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (Gamma : List Ty) (q r : Packed Symbol arity Gamma),packedEqual q r=true ↔ q=r

def ActualLabelBound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),LabelsAtMost (maxLabel q) q

def ActualPrimaryClassBounds : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (Gamma : List Ty) (q r : Packed Symbol arity Gamma),
  WindowPrimary Symbol arity symbols S Gamma q r →
  NumberedPrimaryEquivalence.size q.2=NumberedPrimaryEquivalence.size r.2 ∧ LabelsAtMost (maxLabel q.2) r.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingTargets
