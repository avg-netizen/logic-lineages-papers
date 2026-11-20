module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowTypedProbe (probe)
open NumberedWindowInternalFreshProbeEmitter (calibrated chooseFresh)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalSparsePathEnvelope (run)

/-- Positive original decoding exposes the actual raw sparse fields.
The original decoded context must repack to this same raw coordinate;
typed context validation is not replaced by arity recognition. -/
def ExactOriginalAddressArrowCoordinates : Prop :=
  ∀ (q : Nat) (ctx : List Nat) (r k dom cod : Nat),
    addressView q = some (ctx,r,k) → arrowView r = some (dom,cod) →
      q = packNode 3 [pack ctx,r,k] ∧
      run addressGood q = 1 ∧ run arrowGood q = 1 ∧
      run rawContext q = pack ctx ∧ run rawResult q = r ∧ run rawLeast q = k ∧
      run rawDomain q = dom ∧ run rawCodomain q = cod

/-- All raw inputs of the same actual chosen a use the original probe
Option encoding, including rejection or a legitimate numeric zero
in one of the successful coordinate fields. -/
def ExactParsedFreshCalibration : Prop :=
  ∀ (s : Settings) (scalarProg bound : Program 1), InputCalibrated s scalarProg bound →
    let p := selected scalarProg bound
    calibrated s p ∧
    ∀ q, evaluate (chooseFresh p) (q ::ᵥ nil) = Encodable.encode (probe s q)

def ExactOriginalParsedFreshSelection : Prop :=
  ∀ s : Settings, ∃ scalarProg bound : Program 1,
    InputCalibrated s scalarProg bound ∧
    let p := selected scalarProg bound
    calibrated s p ∧
    ∀ q, evaluate (chooseFresh p) (q ::ᵥ nil) = Encodable.encode (probe s q)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericTargets
