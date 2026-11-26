module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalContextInsertion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-side choice between the two unchanged raw transformation programs. -/
def selectedMode (erasing : Bool) : Mode := if erasing then .erase else .shift

/-- This is the actual original checker graph, not a replacement validity
predicate. False selects terms and true selects argument lists. -/
def Accepted {alpha : Type} (H : Program 1) (arguments : Bool)
    (typ raw gamma : OTerm alpha) : Formula alpha :=
  graph3 (if arguments then OriginalTypedDecoder.argumentsCheck H
    else OriginalTypedDecoder.termCheck H) (numeral 1) typ raw gamma

/-- The source and destination contexts reverse only for erasure. -/
def sourceContext {alpha : Type} (erasing : Bool) (gamma extended : OTerm alpha) : OTerm alpha :=
  if erasing then extended else gamma

def targetContext {alpha : Type} (erasing : Bool) (gamma extended : OTerm alpha) : OTerm alpha :=
  if erasing then gamma else extended

/-- A local forward implication. All inputs, including each binder's own
cutoff, are bound by AtRaw below. Neither successful children nor smaller
transformed raw codes occur in its premise. -/
def Transport {alpha : Type} (H : Program 1) (erasing arguments : Bool)
    (d cutoff gamma extended typ raw transformed : OTerm alpha) : Formula alpha :=
  (Insert d cutoff gamma extended ⊓
    (graph3 (fold (selectedMode erasing)) transformed d cutoff raw ⊓
      Accepted H arguments typ raw (sourceContext erasing gamma extended))).imp
    (Accepted H arguments typ transformed (targetContext erasing gamma extended))

/-- Six universally bound arbitrary arithmetic parameters: erased type,
cutoff, original context, extended context, requested type/list, transformed
raw code. The term and argument claims are proved together by strong raw
induction, so constructor children have their exact original mode. -/
def transportMatrix {alpha : Type} (H : Program 1) (erasing : Bool) (raw : OTerm alpha) :
    Formula (alpha ⊕ Fin 6) :=
  let v : Fin 6 → OTerm (alpha ⊕ Fin 6) := fun i => .var (.inr i)
  Transport H erasing false (v 0) (v 1) (v 2) (v 3) (v 4) (raw.relabel Sum.inl) (v 5) ⊓
    Transport H erasing true (v 0) (v 1) (v 2) (v 3) (v 4) (raw.relabel Sum.inl) (v 5)

def AtRaw {alpha : Type} (H : Program 1) (erasing : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (transportMatrix H erasing raw)

def rawPredicate {alpha : Type} (H : Program 1) (erasing : Bool) : Formula (alpha ⊕ Fin 1) :=
  AtRaw H erasing (.var (.inr 0))

def BelowRaw {alpha : Type} (H : Program 1) (erasing : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (rawPredicate H erasing) raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransport
