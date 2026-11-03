module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits RecursiveNaturalDomains ActualValueLogicalRelation LogicalRelationWorlds

def PortRenameIdentity : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (τ : Ty) (v : Variable (portTypes P.val++I.context) τ),
  portRename (I := I) (P := P) (Q := P) (fun _ hp => hp) v=v

def PortRenameComposition : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P Q R : World I) (h : Extends P Q) (k : Extends Q R) (τ : Ty) (v : Variable (portTypes P.val++I.context) τ),
  portRename k (portRename h v)=portRename (fun p hp => k p (h p hp)) v

def RelatedWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Value I τ P) (q : SyntaxAt I τ P),
  Related I above τ P a q → Related I above τ Q (weaken h a) (futureSyntax h q)

def LiteralVariableRelated : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (v : Variable (portTypes P.val++I.context) τ),
  Related I above τ P (LiteralVariableValueProof.variableValue v) (.var v)

end LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsTargets
