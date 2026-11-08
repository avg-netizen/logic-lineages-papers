module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMap
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact all-input calibration of the original canonical application vertex
at a fixed ambient Gamma. Inputs are [context,domain,codomain,argument,value]. -/
def VertexCalibrated (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (vertexProgram : Program 5) : Prop :=
  ∀ v : List.Vector Nat 5,
    evaluate vertexProgram v = ApplicationCertificateLiftPath.vertex n arity Gamma
      (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)

/-- Read the vertex of the original pair-coded entry. The five inputs are
[entry,context,domain,codomain,argument]. -/
def entryVertex (vertexProgram : Program 5) : Program 5 :=
  .composition vertexProgram
    ![.projection 1,.projection 2,.projection 3,.projection 4,leftOf (.projection 0)]

/-- Read the original edge certificate and use the explicit unchanged
application-edge transformer on [domain,codomain,argument,edge]. -/
def entryEdge : Program 5 :=
  .composition InternalApplicationCertificateConstructors.edgeLift
    ![.projection 2,.projection 3,.projection 4,rightOf (.projection 0)]

/-- One transformed entry in the original pair representation. -/
def entry (vertexProgram : Program 5) : Program 5 :=
  pairOf (entryVertex vertexProgram) entryEdge

/-- The original raw-list map applied to entries. Inputs are
[certificate,context,domain,codomain,argument]; Gamma belongs to the selected
vertex program, not to a new certificate field. -/
def pathMap (vertexProgram : Program 5) : Program 5 :=
  InternalListMap.map (entry vertexProgram)

def parameters {α : Type} (context domain codomain argument : OTerm α) : Fin 4 → OTerm α :=
  Fin.cons context (Fin.cons domain (Fin.cons codomain (Fin.cons argument Fin.elim0)))

def vertexArguments {α : Type} (context domain codomain argument value : OTerm α) :
    Fin 5 → OTerm α :=
  Fin.cons context (Fin.cons domain (Fin.cons codomain
    (Fin.cons argument (Fin.cons value Fin.elim0))))

def entryGraph {α : Type} (vertexProgram : Program 5)
    (out raw context domain codomain argument : OTerm α) : Formula α :=
  programGraph (entry vertexProgram) out
    (Fin.cons raw (parameters context domain codomain argument))

def mapGraph {α : Type} (vertexProgram : Program 5)
    (out code context domain codomain argument : OTerm α) : Formula α :=
  programGraph (pathMap vertexProgram) out
    (Fin.cons code (parameters context domain codomain argument))

/-- The source entry and its two transformed fields are actual graph
witnesses. No typedness, step acceptance, or path acceptance is asserted. -/
def entryPremises {α : Type} (vertexProgram : Program 5)
    (context domain codomain argument raw value edge mappedValue mappedEdge : OTerm α) : Formula α :=
  graph2 InternalPairing.pairing raw value edge ⊓
    (programGraph vertexProgram mappedValue (vertexArguments context domain codomain argument value) ⊓
      graph4 InternalApplicationCertificateConstructors.edgeLift mappedEdge domain codomain argument edge)

def consPremises {α : Type} (vertexProgram : Program 5)
    (context domain codomain argument code raw tail value edge mappedValue mappedEdge mappedRaw mappedTail :
      OTerm α) : Formula α :=
  graph2 InternalListCodec.consCode code raw tail ⊓
    (entryPremises vertexProgram context domain codomain argument raw value edge mappedValue mappedEdge ⊓
      (graph2 InternalPairing.pairing mappedRaw mappedValue mappedEdge ⊓
        mapGraph vertexProgram mappedTail tail context domain codomain argument))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMap
