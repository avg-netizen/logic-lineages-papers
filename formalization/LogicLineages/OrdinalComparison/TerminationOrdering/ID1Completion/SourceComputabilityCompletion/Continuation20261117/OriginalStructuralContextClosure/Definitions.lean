module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Definitions
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

/-- Internal child preservation at every requested type/list, local context and
outer context. No target success is assumed without source success. -/
def TransferMatrix {alpha : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (arguments : Bool) (source target : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  let v : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  (Checked n arity M W arguments (v 0) (source.relabel Sum.inl) (v 1) (v 2)).imp
    (Checked n arity M W arguments (v 0) (target.relabel Sum.inl) (v 1) (v 2))

def Transfer {alpha : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (arguments : Bool) (source target : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (TransferMatrix n arity M W arguments source target)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Definitions
