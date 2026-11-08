module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatch
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The exact original outer pathValue contract, on EVERY natural input in
the order [context,domain,codomain,argumentObject,certificate]. -/
def PathValueCalibrated (n : Nat) (arity : Fin n → Nat) (lift : Program 5) : Prop :=
  ∀ xs : List.Vector Nat 5,
    evaluate lift xs = ApplicationCertificateLiftPath.pathValue n arity xs

/-- Test the original object's LEFT pair coordinate against the fixed Gamma
code. This is independent of the separately selected finite window. -/
def fiberTest (Gamma : List Ty) : Program 5 :=
  InternalApplicationStepPeel.same (leftOf (.projection 3))
    (InternalCanonicalFixedWindowVertexDispatch.constant 5 (Encodable.encode Gamma))

/-- The existing pathMap receives [certificate,context,domain,codomain,RAW
right(argumentObject)]. Its AST, entries, edgeLift and output are unchanged. -/
def activeBranch (vertexProgram : Program 5) : Program 5 :=
  .composition (InternalApplicationPathMap.pathMap vertexProgram)
    ![.projection 4,.projection 0,.projection 1,.projection 2,rightOf (.projection 3)]

/-- A fixed-object-fiber dispatch around the ORIGINAL outer path program.
The inactive branch is oldLift itself, with ALL FIVE inputs unchanged. -/
def dispatch (Gamma : List Ty) (vertexProgram oldLift : Program 5) : Program 5 :=
  InternalAcceptance.branch (fiberTest Gamma) oldLift (activeBranch vertexProgram)

def arguments {α : Type} (context domain codomain argumentObject certificate : OTerm α) :
    Fin 5 → OTerm α :=
  Fin.cons context (Fin.cons domain (Fin.cons codomain
    (Fin.cons argumentObject (Fin.cons certificate Fin.elim0))))

def fiberTestGraph {α : Type} (Gamma : List Ty)
    (out context domain codomain argumentObject certificate : OTerm α) : Formula α :=
  programGraph (fiberTest Gamma) out
    (arguments context domain codomain argumentObject certificate)

def dispatchGraph {α : Type} (Gamma : List Ty) (vertexProgram oldLift : Program 5)
    (out context domain codomain argumentObject certificate : OTerm α) : Formula α :=
  programGraph (dispatch Gamma vertexProgram oldLift) out
    (arguments context domain codomain argumentObject certificate)

def oldLiftGraph {α : Type} (oldLift : Program 5)
    (out context domain codomain argumentObject certificate : OTerm α) : Formula α :=
  programGraph oldLift out (arguments context domain codomain argumentObject certificate)

/-- These are actual graphs of the existing unpair ASTs, not external
decoder equalities or a definition replacing the graphs by arithmetic facts. -/
def fiberCoordinates {α : Type} (Gamma : List Ty)
    (argumentObject argument : OTerm α) : Formula α :=
  graph1 InternalUnpair.left (numeral (Encodable.encode Gamma)) argumentObject ⊓
    graph1 InternalUnpair.right argument argumentObject

/-- Conclusions about ONE fixed selection. No decoding/reflection principle,
path-preservation law or correctness field is supplied as data. -/
def InternalLaws (Gamma : List Ty) (vertexProgram oldLift : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)),
    (∀ (argumentObject argument : OTerm α),
      Nonempty (Derivation body Delta
        ((graph2 InternalPairing.pairing argumentObject
            (numeral (Encodable.encode Gamma)) argument).iff
          (fiberCoordinates Gamma argumentObject argument)))) ∧
    (∀ (context domain codomain argumentObject argument certificate out : OTerm α),
      Nonempty (Derivation body Delta
        ((fiberCoordinates Gamma argumentObject argument).imp
          ((dispatchGraph Gamma vertexProgram oldLift
              out context domain codomain argumentObject certificate).iff
            (InternalApplicationPathMap.mapGraph vertexProgram
              out certificate context domain codomain argument))))) ∧
    (∀ (context domain codomain argumentObject certificate out : OTerm α),
      Nonempty (Derivation body Delta
        ((fiberTestGraph Gamma OrdinaryArithmetic.zeroTerm
            context domain codomain argumentObject certificate).imp
          ((dispatchGraph Gamma vertexProgram oldLift
              out context domain codomain argumentObject certificate).iff
            (oldLiftGraph oldLift out context domain codomain argumentObject certificate))))) ∧
    (∀ (context domain codomain argumentObject leftCode certificate out : OTerm α),
      Nonempty (Derivation body Delta
        (((graph1 InternalUnpair.left leftCode argumentObject) ⊓
            (InternalControlGraph.equal leftCode (numeral (Encodable.encode Gamma))).not).imp
          ((dispatchGraph Gamma vertexProgram oldLift
              out context domain codomain argumentObject certificate).iff
            (oldLiftGraph oldLift out context domain codomain argumentObject certificate)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatch
