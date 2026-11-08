module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatch
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME already selected original leaves. No graph law, calibration,
canonicality, invariant preservation or application lift is a data field. -/
abbrev Data := InternalCertifiedSourceGuardSelection.Data

/-- A literal constant AST, formed using only zero, successor and composition.
The fixed window code is not a new runtime input or an ambient Gamma code. -/
def constant (n : Nat) : Nat → Program n
  | 0 => InternalAcceptance.constantZero n
  | k + 1 => .composition .succ (fun _ : Fin 1 => constant n k)

/-- Original successor-of-pair arrow code, including on arbitrary naturals. -/
def arrowCode (domain codomain : Nat) : Nat := 1 + Nat.pair domain codomain

/-- All five coordinates are [context,domain,codomain,argument,value]. -/
def functionTyped (data : Data) : Program 5 :=
  .composition (InternalCertifiedSourceGuardSelection.typedChecker data)
    ![.projection 4,consOf (.projection 1) (.projection 2)]

def argumentTyped (data : Data) : Program 5 :=
  .composition (InternalCertifiedSourceGuardSelection.typedChecker data)
    ![.projection 3,.projection 1]

/-- The context equality is to contextCode symbols S table when selected.
Gamma remains fixed in leaf calibration, and is NOT this runtime coordinate.
Both typed guards use the SAME selected canonical typed checker, including
its actual successful-run and normalizer fixed-point tests. -/
def activation (window : Nat) (data : Data) : Program 5 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same (.projection 0) (constant 5 window))
    (InternalAcceptance.conjunction (functionTyped data) (argumentTyped data))

/-- The actual previously frozen C, with inputs [domain,codomain,value,argument].
No extra normalization, canonicality test or new representative is inserted. -/
def activeBranch (data : Data) : Program 5 :=
  .composition (InternalRepresentativeFoldCalibration.combine data.oldEdge)
    ![.projection 1,.projection 2,.projection 4,.projection 3]

/-- The zero branch is literally the complete OLD five-input vertex. Thus
off-window and rejected inputs retain all old behavior, not a new zero default.
The actual exact-one conjunction activates only the C branch. -/
def vertex (window : Nat) (data : Data) (oldVertex : Program 5) : Program 5 :=
  InternalAcceptance.branch (activation window data) oldVertex (activeBranch data)

/-- External acceptance condition. It assumes neither successful decoding nor
canonical output, and places no restriction on the five natural inputs. -/
def Active (window : Nat) (data : Data)
    (context domain codomain argument value : Nat) : Prop :=
  context = window ∧
    (evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
      (List.Vector.ofFn ![value,arrowCode domain codomain]) = 1 ∧
      evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
        (List.Vector.ofFn ![argument,domain]) = 1)

def activationAccepted {α : Type} (window : Nat) (data : Data)
    (context domain codomain argument value : OTerm α) : Formula α :=
  programGraph (activation window data) InternalOriginalStepGuard.one
    (InternalApplicationPathMap.vertexArguments context domain codomain argument value)

/-- The actual arrow-constructor output is supplied separately by its graph.
The remaining factors retain both selected typed graphs on symbolic terms. -/
def activationFactors {α : Type} (window : Nat) (data : Data)
    (context domain argument value arrow : OTerm α) : Formula α :=
  InternalControlGraph.equal context (numeral window) ⊓
    (InternalCertifiedSourceGuardSelection.typedAccepted data value arrow ⊓
      InternalCertifiedSourceGuardSelection.typedAccepted data argument domain)

def vertexGraph {α : Type} (window : Nat) (data : Data) (oldVertex : Program 5)
    (out context domain codomain argument value : OTerm α) : Formula α :=
  programGraph (vertex window data oldVertex) out
    (InternalApplicationPathMap.vertexArguments context domain codomain argument value)

/-- This is the ACTUAL C graph, not a representative equality or an output
typedness assertion. The value and argument order is deliberately reversed
relative to the last two coordinates of the five-input vertex. -/
def combineGraph {α : Type} (data : Data)
    (out domain codomain value argument : OTerm α) : Formula α :=
  graph4 (InternalRepresentativeFoldCalibration.combine data.oldEdge)
    out domain codomain value argument

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatch
