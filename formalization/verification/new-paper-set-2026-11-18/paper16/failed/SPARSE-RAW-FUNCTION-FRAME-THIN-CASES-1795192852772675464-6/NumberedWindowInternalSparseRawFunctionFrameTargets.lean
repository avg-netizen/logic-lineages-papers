module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowRawContextAlgorithm (RawRoot tick)
open NumberedWindowRawApplicationLift (lift)

/-- Complete comparison on every raw input, including bad field codes,
extra fields, type mismatches, and argument changes. -/
def ExactAllRawFunctionFrame : Prop :=
  ∀ q w r, evaluate chosenFrame (q ::ᵥ w ::ᵥ r ::ᵥ nil) = encodeFrame (tagFiveNext q w r)

/-- For literal lift, the original raw tick itself takes exactly this
proper function-context transition, independently of its root checker.
The separately selected arithmetic frame reports that identical child. -/
def ExactLiteralFunctionFrame : Prop :=
  ∀ (root : RawRoot) (status : Bool) (dom cod argument source witness dest : Nat),
    let outer := lift dom cod argument source witness dest
    tick root (status,some outer) = (false,some (source,witness,dest)) ∧
    evaluate chosenFrame (outer.1 ::ᵥ outer.2.1 ::ᵥ outer.2.2 ::ᵥ nil) =
      encodeFrame (some (source,witness,dest))

def auxiliaryTerm {α : Type} (dom cod fn arg : OTerm α) : OTerm α :=
  rawCons (numeral 6) (rawCons dom (rawCons cod (rawCons fn (rawCons arg z))))

def functionWitnessTerm {α : Type} (child : OTerm α) : OTerm α :=
  rawCons (numeral 5) (rawCons child z)

def frameValueTerm {α : Type} (source child dest : OTerm α) : OTerm α :=
  suc (rawCons source (rawCons child (rawCons dest z)))

/-- Genuine arbitrary-open graph of that exact selected frame at the
literal lifted original raw triple. The two annotation terms and the
single raw argument are shared. No root/least/syntax guard assertion. -/
def ExactOpenLiteralFunctionFrame : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (dom cod arg source child dest : OTerm α),
    Nonempty (Derivation body [] (programGraph chosenFrame (frameValueTerm source child dest)
      ![auxiliaryTerm dom cod source arg,functionWitnessTerm child,auxiliaryTerm dom cod dest arg]))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
