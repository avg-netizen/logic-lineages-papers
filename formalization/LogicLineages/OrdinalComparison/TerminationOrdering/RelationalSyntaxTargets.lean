module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits RecursiveNaturalDomains TypedValueEnvironment
open CoherentConstructorLattice ConfinedStructuralInterpretation RelatedEnvironments ActualValueLogicalRelation
open RelationalSyntax SourceConstructorIteration ActualComparisonCompleteness TypedObservationAccess RecursiveComparison

/-- Full actual-limit JOINT syntax/scanner/argument fundamental theorem.
No callback body-action, supplied induction hypothesis, relational-equality
identification, mask irrelevance or tuple append law is a premise. -/
def ActualJointFundamental : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol)
    (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above),
  (∀ (Gamma : List Ty) (sigma : Ty) (q : ConfinedTerm I Gamma sigma),
    EvaluationRelated I above (limit I above) q ∧ ScannerRelated I above (limit I above) q) ∧
  (∀ (Gamma types : List Ty) (args : Arguments Symbol arity Gamma types) (ha : ArgumentsConfined I args),
    ArgumentsRelated I above (limit I above) args ha)

def ActualIdentityBitSoundness : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol)
    (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above)
    (P : World I) (sigma : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) sigma)
    (o : ObservationAt I sigma P),
  (readBit false (interpret q (limit I above) P (identity I P)) o.val=true →
    Weak Symbol arity above (portTypes P.val++I.context) ⟨sigma,q.val⟩ ⟨sigma,observedTerm o⟩) ∧
  (readBit true (interpret q (limit I above) P (identity I P)) o.val=true →
    Strict Symbol arity above (portTypes P.val++I.context) ⟨sigma,q.val⟩ ⟨sigma,observedTerm o⟩)

def ActualIdentityAdequacy : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol)
    (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above)
    (P : World I) (sigma : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) sigma)
    (o : ObservationAt I sigma P),
  (readBit false (interpret q (limit I above) P (identity I P)) o.val=true ↔
    Weak Symbol arity above (portTypes P.val++I.context) ⟨sigma,q.val⟩ ⟨sigma,observedTerm o⟩) ∧
  (readBit true (interpret q (limit I above) P (identity I P)) o.val=true ↔
    Strict Symbol arity above (portTypes P.val++I.context) ⟨sigma,q.val⟩ ⟨sigma,observedTerm o⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxTargets
