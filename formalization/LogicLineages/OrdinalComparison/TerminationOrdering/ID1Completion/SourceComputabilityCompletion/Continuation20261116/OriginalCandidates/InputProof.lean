module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.InputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def classQuery (n : Nat) (arity : Fin n → Nat) (H : Program 1) : Program 3 :=
  .composition (OriginalClassCodes.classCodes n arity H) ![.projection 0,.projection 1]
def gammaQuery : Program 3 := .composition OriginalClassCodes.gamma ![.projection 0,.projection 1]
def checkQuery (H : Program 1) : Program 3 :=
  .composition (OriginalTypedDecoder.packedCheck H) ![.projection 2,gammaQuery]
def queries (n : Nat) (arity : Fin n → Nat) (H : Program 1) : Fin 3 → Program 3 :=
  ![classQuery n arity H,gammaQuery,checkQuery H]

theorem classRecover (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (classQuery n arity H) out seed param candidate))) :
    Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.classCodes n arity H) out seed param)) :=
  binaryRecover (OriginalClassCodes.classCodes n arity H) (.projection 0) (.projection 1) out seed param
    ![seed,param,candidate] h (projectionValue 0 ![seed,param,candidate]) (projectionValue 1 ![seed,param,candidate])

theorem gammaRecover (seed param candidate out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 gammaQuery out seed param candidate))) :
    Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma out seed param)) :=
  binaryRecover OriginalClassCodes.gamma (.projection 0) (.projection 1) out seed param
    ![seed,param,candidate] h (projectionValue 0 ![seed,param,candidate]) (projectionValue 1 ![seed,param,candidate])

theorem checkRecover (H : Program 1) (seed param candidate gamma value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (checkQuery H) value seed param candidate)))
    (hg : Nonempty (Derivation body Delta (graph3 gammaQuery gamma seed param candidate))) :
    Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value candidate gamma)) :=
  binaryRecover (OriginalTypedDecoder.packedCheck H) (.projection 2) gammaQuery value candidate gamma
    ![seed,param,candidate] h (projectionValue 2 ![seed,param,candidate]) hg

theorem filterRecover (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out cls gamma : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (candidates n arity H) out seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.classCodes n arity H) cls seed param)))
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param))) :
    Nonempty (Derivation body Delta (graph2 (filterCandidates H) out cls gamma)) :=
  binaryRecover (filterCandidates H) (OriginalClassCodes.classCodes n arity H) OriginalClassCodes.gamma
    out cls gamma ![seed,param] h hc hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.InputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.InputProof
