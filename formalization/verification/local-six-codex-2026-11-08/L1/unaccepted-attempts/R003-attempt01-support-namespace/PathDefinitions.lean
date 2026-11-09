module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Path
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A literal constant built from the original zero and successor ASTs. -/
def constant (n : Nat) : Nat → Program n
  | 0 => InternalAcceptance.constantZero n
  | k + 1 => .composition .succ (fun _ : Fin 1 => constant n k)

/-- The original vertex coordinates now carry [parameter,domain,codomain,
RAWargument,value]. No parameter coordinate enters an edge certificate. -/
abbrev arguments {α : Type} (parameter domain codomain argument value : OTerm α) :
    Fin 5 → OTerm α :=
  InternalApplicationPathMap.vertexArguments parameter domain codomain argument value

def windowAt (window : Program 1) : Program 5 :=
  .composition window (fun _ : Fin 1 => leftOf (.projection 0))

def functionTyped (data : Data) : Program 5 :=
  .composition (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons (.projection 4) (Fin.cons (consOf (.projection 1) (.projection 2))
      (Fin.cons (.projection 0) Fin.elim0)))

def argumentTyped (data : Data) : Program 5 :=
  .composition (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons (.projection 3) (Fin.cons (.projection 1) (Fin.cons (.projection 0) Fin.elim0)))

/-- The global AST reads the context from p. It captures neither a source
window nor an ambient Gamma, and changes the old vertex only on typed inputs
at an admitted window. -/
def activation (data : Data) (window : Program 1) : Program 5 :=
  InternalAcceptance.conjunction (windowAt window)
    (InternalAcceptance.conjunction (functionTyped data) (argumentTyped data))

def activeBranch (data : Data) : Program 5 :=
  .composition (InternalParameterizedCanonicalResultFold.actualJ data)
    (Fin.cons (.projection 1) (Fin.cons (.projection 2) (Fin.cons (.projection 4)
      (Fin.cons (.projection 3) (Fin.cons (.projection 0) Fin.elim0)))))

/-- Inactive inputs retain the COMPLETE original raw vertex output. -/
def vertex (data : Data) (window : Program 1) (oldVertex : Program 5) : Program 5 :=
  InternalAcceptance.branch (activation data window) oldVertex (activeBranch data)

def closedFunctionTyped (data : Data) (sigma tau : Ty) : Program 5 :=
  .composition (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons (.projection 4) (Fin.cons (constant 5 (typeNumber (.arrow sigma tau)))
      (Fin.cons (.projection 0) Fin.elim0)))

def closedArgumentTyped (data : Data) (sigma : Ty) : Program 5 :=
  .composition (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons (.projection 3) (Fin.cons (constant 5 (typeNumber sigma))
      (Fin.cons (.projection 0) Fin.elim0)))

/-- Only the function changes along a path. This arithmetic invariant
records the source context, the unchanged closed type coordinates, and the
same two typed graphs. It assumes no path, output type, or application law. -/
def invariant (context : Nat) (data : Data) (sigma tau : Ty) : Program 5 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same (leftOf (.projection 0)) (constant 5 context))
    (InternalAcceptance.conjunction
      (InternalApplicationStepPeel.same (.projection 1) (constant 5 (typeNumber sigma)))
      (InternalAcceptance.conjunction
        (InternalApplicationStepPeel.same (.projection 2) (constant 5 (typeNumber tau)))
        (InternalAcceptance.conjunction (closedFunctionTyped data sigma tau)
          (closedArgumentTyped data sigma))))

def windowCalibrated (n : Nat) (window : Program 1) : Prop :=
  ∀ v : List.Vector Nat 1, evaluate window v = GuardCalibration.validWindowValue n v

def invariantFactors {α : Type} (context : Nat) (data : Data) (sigma tau : Ty)
    (parameter domain codomain argument value : OTerm α) : Formula α :=
  graph1 InternalUnpair.left (numeral context) parameter ⊓
    (equal domain (numeral (typeNumber sigma)) ⊓
      (equal codomain (numeral (typeNumber tau)) ⊓
        (typedAccepted data value (numeral (typeNumber (.arrow sigma tau))) parameter ⊓
          typedAccepted data argument (numeral (typeNumber sigma)) parameter)))

/-- The concrete input has no supplied path invariant or target typedness.
Both actual vertex outputs and the original mapper's supplied output remain
literal graph premises, at the SAME symbolic runtime Gamma parameter. -/
def positivePremises {α : Type} (context : Nat) (data : Data) (oldStep : Program 4)
    (window : Program 1) (oldVertex : Program 5) (sigma tau : Ty)
    (parameter gammaCode x y argument certificate out other mapped : OTerm α) : Formula α :=
  let ps := InternalApplicationPathMap.parameters parameter
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument
  InternalOriginalUniformApplicationTyping.parameterGraph context parameter gammaCode ⊓
    (typedAccepted data x (numeral (typeNumber (.arrow sigma tau))) parameter ⊓
      (typedAccepted data argument (numeral (typeNumber sigma)) parameter ⊓
        (InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
          x y certificate parameter ⊓
          (InternalParameterizedApplicationPathLift.vertexAt (vertex data window oldVertex) ps out x ⊓
            (InternalParameterizedApplicationPathLift.vertexAt (vertex data window oldVertex) ps other y ⊓
              InternalParameterizedApplicationPathLift.mappedAt (vertex data window oldVertex)
                ps mapped certificate)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Path
