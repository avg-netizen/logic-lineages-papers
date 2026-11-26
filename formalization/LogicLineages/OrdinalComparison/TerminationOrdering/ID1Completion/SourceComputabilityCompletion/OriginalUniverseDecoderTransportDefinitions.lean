module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalContextInsertion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)

/-- Actual original guarded checker graph at its unchanged raw+1 budget. -/
def Accepted {alpha : Type} (H : Program 1) (M W : Program 2) (arguments : Bool)
    (typ raw gamma c : OTerm alpha) : Formula alpha :=
  programGraph (if arguments then OriginalUniverseDecoder.argumentsCheck H M W
    else OriginalUniverseDecoder.termCheck H M W) (numeral 1) ![typ,raw,gamma,c]

/-- A local forward implication. All inputs, including each binder's own
cutoff, are bound by AtRaw below. Neither successful children nor smaller
transformed raw codes occur in its premise. -/
def Transport {alpha : Type} (H : Program 1) (M W : Program 2) (erasing arguments : Bool)
    (d cutoff gamma extended typ raw transformed c : OTerm alpha) : Formula alpha :=
  (Insert d cutoff gamma extended ⊓
    (graph3 (fold (selectedMode erasing)) transformed d cutoff raw ⊓
      Accepted H M W arguments typ raw (sourceContext erasing gamma extended) c)).imp
    (Accepted H M W arguments typ transformed (targetContext erasing gamma extended) c)

/-- Seven universally bound arbitrary arithmetic parameters: erased type,
cutoff, original context, extended context, requested type/list, transformed
raw code and outer context. The term and argument claims are proved together by strong raw
induction, so constructor children have their exact original mode. -/
def transportMatrix {alpha : Type} (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha) :
    Formula (alpha ⊕ Fin 7) :=
  let v : Fin 7 → OTerm (alpha ⊕ Fin 7) := fun i => .var (.inr i)
  Transport H M W erasing false (v 0) (v 1) (v 2) (v 3) (v 4) (raw.relabel Sum.inl) (v 5) (v 6) ⊓
    Transport H M W erasing true (v 0) (v 1) (v 2) (v 3) (v 4) (raw.relabel Sum.inl) (v 5) (v 6)

def AtRaw {alpha : Type} (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (transportMatrix H M W erasing raw)

def rawPredicate {alpha : Type} (H : Program 1) (M W : Program 2) (erasing : Bool) : Formula (alpha ⊕ Fin 1) :=
  AtRaw H M W erasing (.var (.inr 0))

def BelowRaw {alpha : Type} (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (rawPredicate H M W erasing) raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransport
