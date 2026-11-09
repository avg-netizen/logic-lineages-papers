module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentative
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Preserve the WHOLE original packed variable value, not only its Boolean
flag. Nonvariables have mark zero; variables have mark pair(1,value), so raw
variable code zero cannot collide with the nonvariable mark. Exact-one
normalization also specifies every arbitrary symbolic test output. -/
def variableMark : Program 1 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
      OriginalConstructorLeaf.variableTest)
    (InternalAcceptance.constantZero 1)
    (pairOf (InternalLessThan.constantOne 1) (.projection 0))

/-- This is literally the existing eventual validator's active guard. Its
AST does not depend on oldRepresentative. The original bottom-parameter and
member normalization occur only in the unchanged OuterSelection pipeline. -/
def active (data : Data) (window : Program 1) : Program 2 :=
  SpineRepresentative.active data window

def sameMark (oldRepresentative : Program 2) : Program 2 :=
  InternalApplicationStepPeel.same
    (.composition variableMark (fun _ : Fin 1 => oldRepresentative))
    (.composition variableMark (fun _ : Fin 1 => .projection 0))

/-- The inactive original value is retained. On an active mark mismatch,
return the WHOLE raw input, without changing any original encoding. The
all-input equality target must prove that this fallback is natively redundant. -/
def representative (data : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch (active data window) data.oldRepresentative
    (InternalAcceptance.branch (sameMark data.oldRepresentative)
      (.projection 0) data.oldRepresentative)

def baseData (data : Data) (window : Program 1) : Data :=
  { data with oldRepresentative := representative data window }

/-- The actual original pipeline, not a new canonical-fold construction. -/
def selectedData (data : Data) (window : Program 1) : Data :=
  OuterSelection.data (baseData data window) window

def windowGraph {α : Type} (window : Program 1) (input parameter : OTerm α) : Formula α :=
  graph2 (BottomRepresentative.windowAt window) InternalOriginalStepGuard.one input parameter

def markGraph {α : Type} (mark value : OTerm α) : Formula α :=
  graph1 variableMark mark value

/-- Preservation by the ACTUAL selected bounded-descent representative.
No native calibration, assumed invariant, or decoded semantic fact is an
internal antecedent. This supporting property alone is not full fold rigidity. -/
def SelectedMarkPreservation (selected : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (out input parameter mark : OTerm α),
  Nonempty (Derivation body Delta
    ((windowGraph window input parameter ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity selected)
          InternalOriginalStepGuard.one input parameter ⊓
        graph2 (InternalOriginalUniformDescentSelection.representative selected)
          out input parameter)).imp
      ((markGraph mark out).iff (markGraph mark input))))

/-- BOTH directions at the ACTUAL full canonical fold. In particular, a
variable output forces the original raw input to be that same variable.
Window, source validity, outer type and fold output are literal supplied
Program graphs. The original raw type and parameter are not decoded or
fixed externally, and Delta is arbitrary. This is not just forward fixedness. -/
def FullFoldRigidity (selected : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (out input typeCode parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises selected input typeCode parameter ⊓
        (InternalParameterizedCanonicalResultFold.foldGraph selected out input parameter ⊓
          (graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one input ⊔
            graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one out)))).imp
      (equal out input)))

/-- Start with the SAME globally selected original tuple and its paid step
refinement. Only base.oldRepresentative is additionally guarded, BEFORE any
window/Gamma is introduced. In particular oldStep is exactly the once-refined
oldStep, never refined again or selected independently. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  let q := OriginalConstructorLeaf.refineInputs p
  { q with base := baseData q.base q.window }

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentative
