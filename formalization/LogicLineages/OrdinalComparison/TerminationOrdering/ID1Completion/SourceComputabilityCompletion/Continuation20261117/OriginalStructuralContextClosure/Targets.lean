module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Definitions

def InternalLambda : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain child changed : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 lambdaConstructor left domain child)) →
  Nonempty (Derivation body Delta (graph2 lambdaConstructor right domain changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right))

def InternalApplicationFunction : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain child changed sibling : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 applicationConstructor left domain child sibling)) →
  Nonempty (Derivation body Delta (graph3 applicationConstructor right domain changed sibling)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right))

def InternalApplicationArgument : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain sibling child changed : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 applicationConstructor left domain sibling child)) →
  Nonempty (Derivation body Delta (graph3 applicationConstructor right domain sibling changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right))

def InternalOrdinaryBase : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right head child changed : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 ordinaryConstructor left head child)) →
  Nonempty (Derivation body Delta (graph2 ordinaryConstructor right head changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right))

def InternalNumberedBase : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right label head recorded child changed extraTypes extras : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,child,extraTypes,extras])) →
  Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,changed,extraTypes,extras])) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right))

def InternalNumberedExtras : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right label head recorded base extraTypes child changed : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,base,extraTypes,child])) →
  Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,base,extraTypes,changed])) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right))

def InternalArgumentsHead : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain child changed tail : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 consConstructor left domain child tail)) →
  Nonempty (Derivation body Delta (graph3 consConstructor right domain changed tail)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true left right))

def InternalArgumentsTail : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain head child changed : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 consConstructor left domain head child)) →
  Nonempty (Derivation body Delta (graph3 consConstructor right domain head changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true left right))

/-- One combined structural-context bridge; not full exchange preservation. -/
def InternalStructuralContextClosure : Prop :=
  InternalLambda ∧
  InternalApplicationFunction ∧
  InternalApplicationArgument ∧
  InternalOrdinaryBase ∧
  InternalNumberedBase ∧
  InternalNumberedExtras ∧
  InternalArgumentsHead ∧
  InternalArgumentsTail
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Targets
