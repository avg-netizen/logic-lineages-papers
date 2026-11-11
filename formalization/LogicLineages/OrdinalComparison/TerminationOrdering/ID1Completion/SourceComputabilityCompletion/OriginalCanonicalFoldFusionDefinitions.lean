module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The comparison is between actual binary Program graphs. No semantic
function, replacement machine or successful-run premise occurs here. -/
def outputInvariant {alpha : Type} (_data : Data) (_window : Program 1)
    (_source target : Program 2)
    (out input _typ parameter : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  graph2 target out input parameter

/-- The original window and actual source/type accompany the source graph. -/
def premises {alpha : Type} (data : Data) (window : Program 1) (source _target : Program 2)
    (out input typ parameter : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises data input typ parameter ⊓
      graph2 source out input parameter)

/-- All four terms stay inside the induction predicate. In particular the
source parameter is not fixed outside internal strong-payload induction. -/
def payloadMatrix {alpha : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 4) :=
  let input : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 3)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    ((premises data window source target out input typ parameter).imp
      (outputInvariant data window source target out input typ parameter))

def atPayload {alpha : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix data window source target payload)

def payloadPredicate (data : Data) (window : Program 1) (source target : Program 2) {alpha : Type} :
    Formula (alpha ⊕ Fin 1) := atPayload data window source target (.var (.inr 0))

def belowPayload {alpha : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate data window source target) payload

/-- A proof-valued closed-branch supplier, discharged at each concrete fold.
It does not change a Program or add any premise to the final frozen targets. -/
def ClosedLaw (data : Data) (window : Program 1) (source target : Program 2) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation positive Delta (premises data window source target out input typ parameter)) →
    Nonempty (Derivation positive Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard data)) OrdinaryArithmetic.zeroTerm input parameter)) →
    Nonempty (Derivation positive Delta (outputInvariant data window source target out input typ parameter))

/-- The application branch receives precisely the two smaller-payload
comparison conclusions. Actual constructors and original graphs are retained. -/
def ApplicationLaw (data : Data) (window : Program 1) (source target : Program 2) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (arrow d e fp ap fn arg input functionOut argumentOut out typ parameter : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation positive Delta
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg input)) →
    Nonempty (Derivation positive Delta (premises data window source target out input typ parameter)) →
    Nonempty (Derivation positive Delta (graph2 source functionOut fn parameter)) →
    Nonempty (Derivation positive Delta (graph2 source argumentOut arg parameter)) →
    Nonempty (Derivation positive Delta (graph2 target functionOut fn parameter)) →
    Nonempty (Derivation positive Delta (graph2 target argumentOut arg parameter)) →
    Nonempty (Derivation positive Delta (outputInvariant data window source target out input typ parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusion
