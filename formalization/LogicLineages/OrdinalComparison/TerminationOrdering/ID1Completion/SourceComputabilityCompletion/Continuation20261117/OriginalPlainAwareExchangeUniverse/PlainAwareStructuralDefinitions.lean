module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The original guarded checker, with its original raw-dependent budget. -/
def Checked {alpha : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (arguments : Bool) (typ raw gamma context : OTerm alpha) : Formula alpha :=
  programGraph (if arguments then OriginalUniverseDecoder.argumentsCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W
    else OriginalUniverseDecoder.termCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
    (suc z) ![typ,raw,gamma,context]

/-- Original plain checker at the SAME requested type and gamma. -/
def Plain {alpha : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
 (typ raw gamma : OTerm alpha) : Formula alpha :=
 OriginalTypedDecoderTransport.Accepted (Continuation20261116.OriginalConcreteHeadSignature.signature n arity)
  arguments typ raw gamma
/-- Context is fixed by the exchange window. Only requested type and gamma vary. -/
def TransferMatrix {alpha : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
 (arguments : Bool) (source target context : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 let v : Fin 2 → OTerm (alpha ⊕ Fin 2) := fun i => .var (.inr i)
 ((Checked n arity M W arguments (v 0) (source.relabel Sum.inl) (v 1) (context.relabel Sum.inl)) ⊓
  (Plain n arity arguments (v 0) (target.relabel Sum.inl) (v 1))).imp
  (Checked n arity M W arguments (v 0) (target.relabel Sum.inl) (v 1) (context.relabel Sum.inl))
def Transfer {alpha : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
 (arguments : Bool) (source target context : OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (TransferMatrix n arity M W arguments source target context)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralDefinitions
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PlainAwareStructuralDefinitions

def InternalLambda : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain child changed context : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 lambdaConstructor left domain child)) →
  Nonempty (Derivation body Delta (graph2 lambdaConstructor right domain changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right context))

def InternalApplicationFunction : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain child changed sibling context : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 applicationConstructor left domain child sibling)) →
  Nonempty (Derivation body Delta (graph3 applicationConstructor right domain changed sibling)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right context))

def InternalApplicationArgument : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain sibling child changed context : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 applicationConstructor left domain sibling child)) →
  Nonempty (Derivation body Delta (graph3 applicationConstructor right domain sibling changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right context))

def InternalOrdinaryBase : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right head child changed context : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 ordinaryConstructor left head child)) →
  Nonempty (Derivation body Delta (graph2 ordinaryConstructor right head changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right context))

def InternalNumberedBase : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right label head recorded child changed extraTypes extras context : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,child,extraTypes,extras])) →
  Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,changed,extraTypes,extras])) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right context))

def InternalNumberedExtras : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right label head recorded base extraTypes child changed context : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,base,extraTypes,child])) →
  Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,base,extraTypes,changed])) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false left right context))

def InternalArgumentsHead : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain child changed tail context : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 consConstructor left domain child tail)) →
  Nonempty (Derivation body Delta (graph3 consConstructor right domain changed tail)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true left right context))

def InternalArgumentsTail : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right domain head child changed context : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 consConstructor left domain head child)) →
  Nonempty (Derivation body Delta (graph3 consConstructor right domain head changed)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)) →
  Nonempty (Derivation body Delta (Transfer n arity M W true left right context))

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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralTargets
