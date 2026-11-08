module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationPathMap
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A single actual vertex program is chosen for each fixed Gamma and works
on every five-tuple, including malformed/off-domain natural inputs. -/
def ActualOriginalVertexProgramExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    ∃ vertexProgram : Program 5, VertexCalibrated n arity Gamma vertexProgram

def ActualOriginalEntryCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (vertexProgram : Program 5),
  VertexCalibrated n arity Gamma vertexProgram →
  ∀ v : List.Vector Nat 5,
    evaluate (entry vertexProgram) v =
      Nat.pair
        (ApplicationCertificateLiftPath.vertex n arity Gamma
          (v.get 1) (v.get 2) (v.get 3) (v.get 4) (Nat.unpair (v.get 0)).1)
        (ApplicationCertificateLiftEdge.liftEdge
          (v.get 2) (v.get 3) (v.get 4) (Nat.unpair (v.get 0)).2)

/-- Exact calibration to the existing liftPath on all natural codes. This
does not alter the outer pathValue wrapper's malformed-object fallback. -/
def ActualOriginalPathCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (vertexProgram : Program 5),
  VertexCalibrated n arity Gamma vertexProgram →
  ∀ v : List.Vector Nat 5,
    evaluate (pathMap vertexProgram) v =
      ApplicationCertificateLiftPath.liftPath n arity Gamma
        (v.get 1) (v.get 2) (v.get 3) (v.get 4) (v.get 0)

/-- Internal entry commutation at the original supplied pair fields and
the concrete vertex/edge graph outputs. Calibration is not an internal premise. -/
def ActualOriginalEntryGraphEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (vertexProgram : Program 5) (α : Type)
    (context domain codomain argument raw value edge mappedValue mappedEdge out : OTerm α),
  Nonempty (Derivation body []
    ((entryPremises vertexProgram context domain codomain argument raw value edge mappedValue mappedEdge).imp
      ((entryGraph vertexProgram out raw context domain codomain argument).iff
        (graph2 InternalPairing.pairing out mappedValue mappedEdge))))

def ActualOriginalPathMapZero : Prop :=
  ∀ (body : Positive (Fin 1)) (vertexProgram : Program 5) (α : Type)
    (out context domain codomain argument : OTerm α),
  Nonempty (Derivation body []
    ((mapGraph vertexProgram out OrdinaryArithmetic.zeroTerm context domain codomain argument).iff
      (equal out OrdinaryArithmetic.zeroTerm)))

/-- Literal original path cons, expanded through the actual pair-coded entry,
canonical vertex graph and edge-transformer graph. No edge acceptance is assumed. -/
def ActualOriginalPathMapCons : Prop :=
  ∀ (body : Positive (Fin 1)) (vertexProgram : Program 5) (α : Type)
    (context domain codomain argument code raw tail value edge mappedValue mappedEdge mappedRaw mappedTail out :
      OTerm α),
  Nonempty (Derivation body []
    ((consPremises vertexProgram context domain codomain argument code raw tail value edge
      mappedValue mappedEdge mappedRaw mappedTail).imp
      ((mapGraph vertexProgram out code context domain codomain argument).iff
        (graph2 InternalListCodec.consCode out mappedRaw mappedTail))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapTargets
