module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShape
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal outer constructor tag of the original packed term. -/
def tag : Program 1 := constructorTag (.projection 0)

/-- Read the original application domain only at tag two. Other constructor
payloads have different meanings and are deliberately not observed here. -/
def applicationDomain : Program 1 :=
  InternalAcceptance.branch (same tag (two 1))
    (InternalAcceptance.constantZero 1) (appDomain (.projection 0))

/-- A nonrecursive observer of the actual raw root shape and application
domain. No canonical child code or semantic parser is hidden in this mark. -/
def mark : Program 1 := pairOf tag applicationDomain

def active (data : Data) (window : Program 1) : Program 2 :=
  SpineRepresentative.active data window

def sameMark (representative : Program 2) : Program 2 :=
  same (.composition mark (fun _ : Fin 1 => representative))
    (.composition mark (fun _ : Fin 1 => .projection 0))

/-- Preserve every inactive original output; on an active mark mismatch
return the WHOLE input. Native all-input equality separately pays redundancy. -/
def representative (data : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch (active data window) data.oldRepresentative
    (InternalAcceptance.branch (sameMark data.oldRepresentative)
      (.projection 0) data.oldRepresentative)

def baseData (data : Data) (window : Program 1) : Data :=
  { data with oldRepresentative := representative data window }

/-- The existing variable, spine, bottom, parameter and membership pipeline
is applied after the shape guard. Its Programs and numberings are unchanged. -/
def selectedData (data : Data) (window : Program 1) : Data :=
  OriginalVariableRepresentative.selectedData (baseData data window) window

def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := baseData p.base p.window }

def finalInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalVariableRepresentative.refineInputs
    (OriginalNeutralLeaf.refineInputs (refineInputs p))

abbrev markGraph {alpha : Type} (value input : OTerm alpha) : Formula alpha :=
  graph1 mark value input

abbrev tagGraph {alpha : Type} (value input : OTerm alpha) : Formula alpha :=
  graph1 tag value input

abbrev windowGraph {alpha : Type} (window : Program 1)
    (input parameter : OTerm alpha) : Formula alpha :=
  OriginalVariableRepresentative.windowGraph window input parameter

def applicationShape {alpha : Type} (domain input : OTerm alpha) : Formula alpha :=
  tagGraph InternalApplicationCertificateConstructors.positionTerm input ⊓
    graph1 (appDomain (.projection 0)) domain input

def SelectedMarkPreservation (data : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input parameter value : OTerm alpha),
  Nonempty (Derivation body Delta
    ((windowGraph window input parameter ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity data)
          InternalOriginalStepGuard.one input parameter ⊓
        graph2 (InternalOriginalUniformDescentSelection.representative data)
          out input parameter)).imp
      ((markGraph value out).iff (markGraph value input))))

def FullFoldMarkPreservation (data : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typeCode parameter value : OTerm alpha),
  Nonempty (Derivation body Delta
    ((windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises data input typeCode parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph data out input parameter)).imp
      ((markGraph value out).iff (markGraph value input))))

/-- Every symbolic tag is preserved and reflected. At applications the
actual original domain code is preserved as well. Native calibration and
an assumed observer invariant are absent from these arithmetic premises. -/
def FullFoldRootFields (data : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typeCode parameter value domain : OTerm alpha),
  Nonempty (Derivation body Delta
    ((windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises data input typeCode parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph data out input parameter)).imp
      (((tagGraph value out).iff (tagGraph value input)) ⊓
        ((applicationShape domain out).iff (applicationShape domain input)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShape
