module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutrality
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The existing original raw neutral test observes precisely tag-two
applications whose actual function payload is not a lambda. Nonapplications
are masked by that same test, so unrelated payloads are not observed. -/
def mark : Program 1 := OriginalNeutralLeaf.neutralTest

def active (data : Data) (window : Program 1) : Program 2 :=
  SpineRepresentative.active data window

def sameMark (representative : Program 2) : Program 2 :=
  same (.composition mark (fun _ : Fin 1 => representative))
    (.composition mark (fun _ : Fin 1 => .projection 0))

/-- On an active neutral-observer mismatch retain the whole original input;
inactive outputs are literal. Native equality separately proves redundancy. -/
def representative (data : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch (active data window) data.oldRepresentative
    (InternalAcceptance.branch (sameMark data.oldRepresentative)
      (.projection 0) data.oldRepresentative)

def baseData (data : Data) (window : Program 1) : Data :=
  { data with oldRepresentative := representative data window }

/-- The existing shape, variable, spine and bottom pipeline follows the
new guard. Its full-fold root-field theorem therefore remains applicable. -/
def selectedData (data : Data) (window : Program 1) : Data :=
  OriginalConstructorShape.selectedData (baseData data window) window

def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := baseData p.base p.window }

def finalInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalConstructorShape.finalInputs (refineInputs p)

abbrev markGraph {alpha : Type} (value input : OTerm alpha) : Formula alpha :=
  graph1 mark value input

abbrev windowGraph {alpha : Type} (window : Program 1)
    (input parameter : OTerm alpha) : Formula alpha :=
  OriginalVariableRepresentative.windowGraph window input parameter

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

/-- Function-level neutrality is preserved and reflected through the SAME
actual canonical fold. The invariant is not supplied as an arithmetic
premise, and no equality with a reconstructed application is assumed. -/
def FullFoldMarkPreservation (data : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typeCode parameter value : OTerm alpha),
  Nonempty (Derivation body Delta
    ((windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises data input typeCode parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph data out input parameter)).imp
      ((markGraph value out).iff (markGraph value input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutrality
