module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowOccurrenceTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedWindowTraces

def PointwiseWindowTrace {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} (qs rs : List (Packed Symbol arity Gamma)) : Prop :=
  List.Forall₂ (fun q r => ∃ n,WindowTrace Symbol arity symbols S above Gamma n q r) qs rs

def ActualPointwiseTupleTarget : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma types : List Ty) (args : AuxArguments Symbol arity Gamma types)
    (values : List (Packed Symbol arity Gamma)),PointwiseWindowTrace symbols S above (argumentList args) values →
    ∃ (n : Nat) (target : AuxArguments Symbol arity Gamma types),argumentList target=values ∧
      WindowTupleTrace Symbol arity symbols S above Gamma types n args target

def ActualPointwiseTupleSource : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma types : List Ty) (target : AuxArguments Symbol arity Gamma types)
    (values : List (Packed Symbol arity Gamma)),PointwiseWindowTrace symbols S above values (argumentList target) →
    ∃ (n : Nat) (source : AuxArguments Symbol arity Gamma types),argumentList source=values ∧
      WindowTupleTrace Symbol arity symbols S above Gamma types n source target

def ActualFiniteMarkStep : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    finiteMark n q=some r → WindowStep Symbol arity symbols S above Gamma tau q r

def ActualOriginalPositiveMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (tau : Ty)
    (q r : MarkedTerm Symbol arity Gamma tau),RecursiveComparison.strictMark q=some r →
    ∀ Q : AuxTerm Symbol arity Gamma tau,Represents Symbol arity (n+1) Gamma tau q Q →
    ∃ R,WindowStep Symbol arity symbols S above Gamma tau Q R ∧ Represents Symbol arity n Gamma tau r R

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowOccurrenceTargets
