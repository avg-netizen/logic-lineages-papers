module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast ActualLeastCalibration)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseApplicationOutputCore (outputCore)

/-- Actual optional output computation in the original canonical
application after its real source guards, on the selected raw values.
Only the output leg is specified here; no active input guard is assumed
or decided by this core on the arbitrary input tape. -/
def originalOutput (s : Settings) (ctx dom cod fn arg : Nat) : Option Nat :=
  (packedLeast s ctx cod (packNode 6 [dom,cod,fn,arg])).map
    (fun k => packNode 3 [ctx,cod,k])

/-- All-input original equality, including zero, undecodable packed
context, absent least, and malformed seed data. Nothing identifies an
unrelated old application program with this AST. -/
def ExactAllInputApplicationOutputCore : Prop :=
  ∀ (s : Settings) (least : Program 3), ActualLeastCalibration s least →
    ∀ ctx dom cod fn arg y,
      evaluate (outputCore least) (ctx ::ᵥ dom ::ᵥ cod ::ᵥ fn ::ᵥ arg ::ᵥ y ::ᵥ nil) =
        ((originalOutput s ctx dom cod fn arg == some y).toNat)

/-- The single successful class code is a genuine object-language
existential. The same witness occurs in the actual optional least
graph and the original output-address equation. -/
def outputReport {α : Type} (least : Program 3) (ctx cod raw y : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (programGraph least (suc k) ![ctx.relabel j,cod.relabel j,raw.relabel j] ⊓
    eqn (y.relabel j) (addressTerm (ctx.relabel j) (cod.relabel j) k))

/-- Genuine arbitrary-open two directions for this physical core, in the
same ID1 body and ordinary context. No numerical premise and no input or
output carrier assertion. The full physical application front end is
a separate obligation. -/
def ExactOpenApplicationOutputCore : Prop :=
  ∀ (body : Positive (Fin 1)) (least : Program 3) (α : Type) (Γ : List (Formula α))
    (ctx dom cod fn arg y : OTerm α),
    let unitGraph := programGraph (outputCore least) (suc z) ![ctx,dom,cod,fn,arg,y]
    let report := outputReport least ctx cod (auxiliaryTerm dom cod fn arg) y
    Nonempty (Derivation body Γ ((unitGraph.imp report) ⊓ (report.imp unitGraph)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets
