module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRoot
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal raw PUT output, including on malformed bytes. The source type,
ordinary head and base are copied; the label is the second original input.
Extra-type list is nil and extra-arguments is the ORIGINAL argumentsNil code. -/
def resultCode : Program 2 :=
  let s : Program 2 := .projection 0
  let typ := leftOf s
  let payload := rightOf (rightOf s)
  let head := leftOf payload
  let base := rightOf payload
  pairOf typ (pairOf (OriginalRawSyntaxTransport.constant 2 5)
    (pairOf (.projection 1) (pairOf head (pairOf typ
      (pairOf base (pairOf (OriginalRawSyntaxTransport.constant 2 0)
        (pairOf (OriginalRawSyntaxTransport.constant 2 6) (OriginalRawSyntaxTransport.constant 2 0))))))))

/-- ORIGINAL [nil,replacement,PUT label] step-certificate layout. -/
def certificateCode : Program 2 :=
  pairOf (OriginalRawSyntaxTransport.constant 2 0)
    (pairOf resultCode (pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 1)))

/-- Read the original root selector's payload; no certificate field is added. -/
def labelOf : Program 1 := rightOf (rightOf (rightOf (.projection 0)))

def labelAt : Program 4 := .composition labelOf (fun _ : Fin 1 => .projection 2)
def resultAt : Program 4 := .composition resultCode ![.projection 0,labelAt]
def certificateAt : Program 4 := .composition certificateCode ![.projection 0,labelAt]

def active : Program 4 := InternalApplicationStepPeel.same (.projection 2) certificateAt

def ordinaryAt : Program 4 :=
  InternalApplicationStepPeel.same (leftOf (rightOf (.projection 0)))
    (OriginalRawSyntaxTransport.constant 4 4)

def acceptedValue (source : Program 2) : Program 4 :=
  InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source)
    (InternalAcceptance.conjunction ordinaryAt
      (InternalApplicationStepPeel.same (.projection 1) resultAt))

/-- Replace exactly the chosen original PUT-certificate branch. Every
inactive input retains the WHOLE old leaf output, including malformed inputs. -/
def refined (source : Program 2) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.branch active oldStep (acceptedValue source)

/-- Install once BEFORE the unchanged prepared/final selection pipeline. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.base.oldSource p.oldStep }

def resultValue (source label : Nat) : Nat :=
  let typ := (Nat.unpair source).1
  let payload := (Nat.unpair (Nat.unpair source).2).2
  Nat.pair typ (Nat.pair 5 (Nat.pair label
    (Nat.pair (Nat.unpair payload).1 (Nat.pair typ
      (Nat.pair (Nat.unpair payload).2 (Nat.pair 0 (Nat.pair 6 0)))))))

def certificateValue (source label : Nat) : Nat :=
  Nat.pair 0 (Nat.pair (resultValue source label) (Nat.pair 0 label))

def labelValue (certificate : Nat) : Nat :=
  (Nat.unpair (Nat.unpair (Nat.unpair certificate).2).2).2

/-- Only actual source acceptance and original constructor/computation graphs.
No oldStep graph, native reflection, root-success or erasure law is supplied. -/
def Premises {alpha : Type} (source : Program 2)
    (s t cert parameter typ raw head base label : OTerm alpha) : Formula alpha :=
  graph2 source InternalOriginalStepGuard.one s parameter ⊓
    (graph2 InternalPairing.pairing s typ raw ⊓
      (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base ⊓
        (graph2 resultCode t s label ⊓ graph2 certificateCode cert s label)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRoot
