module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironmentsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironmentsTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits TypedValueEnvironment ActualValueLogicalRelation
open RelatedEnvironments LambdaObservationMatching

def Weakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (Gamma : List Ty)
    (P Q : World I) (h : Extends P Q) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context)),
  EnvironmentRelated I above P rho s →
    EnvironmentRelated I above Q (restrict h rho) (futureSubstitution h s)

def Extension : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (Gamma : List Ty)
    (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context)) (sigma : Ty)
    (a : RecursiveNaturalDomains.Value I sigma P)
    (q : MarkedTerm Symbol arity (portTypes P.val++I.context) sigma),
  EnvironmentRelated I above P rho s → Related I above sigma P a q →
    EnvironmentRelated I above P (extend a rho) (extendEnvironment s q)

def FreshOpening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (Gamma : List Ty)
    (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
    (sigma upsilon : Ty) (i : Fin (budget I)) (h : MarkedFAbsTest.Opening I P sigma upsilon i),
  EnvironmentRelated I above P rho s →
    EnvironmentRelated I above ⟨(i,sigma)::P.val,h.2.1⟩
      (openingEnvironment rho sigma upsilon i h) (liftSubstitution s)

end LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironmentsTargets
