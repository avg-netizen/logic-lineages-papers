module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets
public import LogicLineages.PersistentMarking.NumberedWindowAddressApplication

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood arrowGood)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressReports arrowReports addressTerm)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowScalarAlgorithm (Settings scalar)

/-- Actual scalar calibration on the whole raw address input, not an
assertion about the underlying class coordinate and not object reflection. -/
def ActualScalarCalibration (s : Settings) (i : Program 1) : Prop :=
  ∀ q, evaluate i (q ::ᵥ nil) = (scalar s q).toNat

/-- Original all-raw canonical application graph at the actual guarded
physical program, with the same original scalar i and actual packed
least calibration. No ValidWindow or input-success premise. -/
def ExactAllInputGuardedApplication : Prop :=
  ∀ (s : Settings) (i : Program 1) (least : Program 3),
    ActualScalarCalibration s i → ActualLeastCalibration s least →
    ∀ f u y, evaluate (applicationGuard i least) (f ::ᵥ u ::ᵥ y ::ᵥ nil) =
      (NumberedWindowAddressApplication.graph s f u y).toNat

/-- Real selected unary graphs plus the literal shared context/domain
equations. Keep the raw source result separate from its arrow components;
the argument's result is exactly the domain, not another arrow. -/
def parsedApplicationInputs {α : Type} (f u ctx result dom cod fn arg : OTerm α) : Formula α :=
  unary addressGood (suc z) f ⊓
    (unary addressGood (suc z) u ⊓
      (unary arrowGood (suc z) f ⊓
        (addressReports f ctx result fn ⊓
          (addressReports u ctx dom arg ⊓
            (arrowReports f dom cod ⊓
              (eqn f (addressTerm ctx result fn) ⊓
                (eqn result (rawCons dom cod) ⊓ eqn u (addressTerm ctx dom arg))))))))

/-- Original function, argument and result remain fixed through this
ordered six-variable block. The nested existing output report has its
own single genuine least witness, shared by the actual least graph
and the final equation for the original output address. -/
def applicationRow {α : Type} (least : Program 3) (f u y : OTerm α) : Formula (α ⊕ Fin 6) :=
  let j : α → α ⊕ Fin 6 := Sum.inl
  let ctx : OTerm (α ⊕ Fin 6) := .var (.inr 0)
  let result : OTerm (α ⊕ Fin 6) := .var (.inr 1)
  let dom : OTerm (α ⊕ Fin 6) := .var (.inr 2)
  let cod : OTerm (α ⊕ Fin 6) := .var (.inr 3)
  let fn : OTerm (α ⊕ Fin 6) := .var (.inr 4)
  let arg : OTerm (α ⊕ Fin 6) := .var (.inr 5)
  parsedApplicationInputs (f.relabel j) (u.relabel j) ctx result dom cod fn arg ⊓
    outputReport least ctx cod (auxiliaryTerm dom cod fn arg) (y.relabel j)

/-- The genuine scalar graphs remain at the two whole original inputs.
The block asserts no scalar admission or other carrier at y. -/
def applicationReport {α : Type} (i : Program 1) (least : Program 3) (f u y : OTerm α) : Formula α :=
  unary i (suc z) f ⊓ (unary i (suc z) u ⊓ block (applicationRow least f u y))

/-- Genuine internal graph equivalence in the same arbitrary body and
ordinary context, with no arithmetic equality reflection or callback
semantics assumed. -/
def ExactOpenGuardedApplication : Prop :=
  ∀ (body : Positive (Fin 1)) (i : Program 1) (least : Program 3)
    (α : Type) (Γ : List (Formula α)) (f u y : OTerm α),
    let accepted := programGraph (applicationGuard i least) (suc z) ![f,u,y]
    let reported := applicationReport i least f u y
    Nonempty (Derivation body Γ ((accepted.imp reported) ⊓ (reported.imp accepted)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
