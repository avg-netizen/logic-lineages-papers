module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceSharpening

def Reflexivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty),
  (∀ tau (q : MarkedTerm Symbol arity Gamma tau),Sharp Symbol arity Gamma q q) ∧
  (∀ types (args : Arguments Symbol arity Gamma types),ArgumentsSharp Symbol arity Gamma args args)

def Retagging : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (f : Head Symbol) (sigma tau : Ty) (baseS baseT : Arguments Symbol arity Gamma (headArguments arity f))
    (typesS typesT : List Ty) (extrasS : Arguments Symbol arity Gamma typesS) (extrasT : Arguments Symbol arity Gamma typesT),
  Sharp Symbol arity Gamma (.marked f sigma baseS typesS extrasS) (.marked f sigma baseT typesT extrasT) →
    Sharp Symbol arity Gamma (.marked f tau baseS typesS extrasS) (.marked f tau baseT typesT extrasT)

def StrictMarkPreservation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (tau : Ty) (q u r : MarkedTerm Symbol arity Gamma tau),
  Sharp Symbol arity Gamma q u → strictMark q=some r →
    ∃ v,strictMark u=some v ∧ Sharp Symbol arity Gamma r v

def RelatedSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (tau : Ty) (q u : MarkedTerm Symbol arity Gamma tau)
    (theta eta : MarkedSubstitution Symbol arity Gamma Delta),
  Sharp Symbol arity Gamma q u → (∀ sigma (v : Variable Gamma sigma),Sharp Symbol arity Delta (theta v) (eta v)) →
    Sharp Symbol arity Delta (substituteTerm q theta) (substituteTerm u eta)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningTargets
