module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatch
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original five outer inputs remain
[context,domain,codomain,argumentObject,certificate]. Only the fixed selected
window is tested; no ambient Gamma is captured by this AST. -/
def windowTest (window : Nat) : Program 5 :=
  InternalApplicationStepPeel.same (.projection 0)
    (InternalCanonicalFixedWindowVertexDispatch.constant 5 window)

/-- The parameter uses the original context and the actual LEFT coordinate
of the original argument Object. Its raw payload is not normalized here. -/
def runtimeParameter : Program 5 :=
  pairOf (.projection 0) (leftOf (.projection 3))

/-- The existing map receives
[certificate,pair(context,left(argumentObject)),domain,codomain,right(argumentObject)].
No path entry, edge certificate, decoder, or list representation is changed. -/
def activeBranch (vertexProgram : Program 5) : Program 5 :=
  .composition (InternalApplicationPathMap.pathMap vertexProgram)
    ![.projection 4,runtimeParameter,.projection 1,.projection 2,rightOf (.projection 3)]

/-- The complete original oldLift handles every other context at the same
five original inputs. The active branch uses the same globally selected vertex. -/
def dispatch (window : Nat) (vertexProgram oldLift : Program 5) : Program 5 :=
  InternalAcceptance.branch (windowTest window) oldLift (activeBranch vertexProgram)

/-- Full original calibration, including arbitrary object and certificate
codes and all inactive context inputs. -/
def PathValueCalibrated (n : Nat) (arity : Fin n → Nat) (lift : Program 5) : Prop :=
  ∀ xs : List.Vector Nat 5,
    evaluate lift xs = ApplicationCertificateLiftPath.pathValue n arity xs

def arguments {α : Type} (context domain codomain argumentObject certificate : OTerm α) :
    Fin 5 → OTerm α :=
  Fin.cons context (Fin.cons domain (Fin.cons codomain
    (Fin.cons argumentObject (Fin.cons certificate Fin.elim0))))

def windowGraph {α : Type} (window : Nat)
    (out context domain codomain argumentObject certificate : OTerm α) : Formula α :=
  programGraph (windowTest window) out
    (arguments context domain codomain argumentObject certificate)

def dispatchGraph {α : Type} (window : Nat) (vertexProgram oldLift : Program 5)
    (out context domain codomain argumentObject certificate : OTerm α) : Formula α :=
  programGraph (dispatch window vertexProgram oldLift) out
    (arguments context domain codomain argumentObject certificate)

def oldLiftGraph {α : Type} (oldLift : Program 5)
    (out context domain codomain argumentObject certificate : OTerm α) : Formula α :=
  programGraph oldLift out (arguments context domain codomain argumentObject certificate)

/-- Both coordinates are genuine original unpair graphs. GammaCode is an
arbitrary arithmetic term, never a supplied decoded List Ty or fixed numeral. -/
def objectCoordinates {α : Type} (gammaCode argumentObject argument : OTerm α) : Formula α :=
  graph1 InternalUnpair.left gammaCode argumentObject ⊓
    graph1 InternalUnpair.right argument argumentObject

/-- The parameter is computed internally by the unchanged pairing program.
These are graph-level inputs to the local equivalence, not semantic facts. -/
def activePremises {α : Type} (window : Nat)
    (context gammaCode argumentObject argument parameter : OTerm α) : Formula α :=
  equal context (numeral window) ⊓
    (objectCoordinates gammaCode argumentObject argument ⊓
      graph2 InternalPairing.pairing parameter context gammaCode)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatch
