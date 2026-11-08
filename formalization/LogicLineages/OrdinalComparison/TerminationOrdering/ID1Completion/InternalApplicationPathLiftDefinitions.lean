module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLift
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalPathChecker InternalClosedPrograms InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Unchanged context, domain, codomain and argument coordinates. -/
abbrev Parameters (α : Type) := Fin 4 → OTerm α

def vertexInputs {α : Type} (ps : Parameters α) (x : OTerm α) : Fin 5 → OTerm α :=
  InternalApplicationPathMap.vertexArguments (ps 0) (ps 1) (ps 2) (ps 3) x

def vertexAt {α : Type} (vertex : Program 5) (ps : Parameters α) (out x : OTerm α) : Formula α :=
  programGraph vertex out (vertexInputs ps x)

/-- A purely arithmetic invariant can record the actual source typing,
window and argument requirements. It is never computability or path closure. -/
def invariantAt {α : Type} (invariant : Program 5) (ps : Parameters α) (x : OTerm α) : Formula α :=
  vertexAt invariant ps (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) x

def liftedEdgeAt {α : Type} (ps : Parameters α) (out certificate : OTerm α) : Formula α :=
  graph4 InternalApplicationCertificateConstructors.edgeLift out (ps 1) (ps 2) (ps 3) certificate

def mappedAt {α : Type} (vertex : Program 5) (ps : Parameters α) (out code : OTerm α) : Formula α :=
  programGraph (InternalApplicationPathMap.pathMap vertex) out (Fin.cons code ps)

/-- The one-edge arithmetic invariant rule. No path conclusion is a premise. -/
def InvariantPreservation (body : Positive (Fin 1)) (edge : Program 3) (invariant : Program 5) : Prop :=
  ∀ (α : Type) (ps : Parameters α) (x y certificate : OTerm α),
  Nonempty (Derivation body []
    ((invariantAt invariant ps x ⊓ edgeGraph edge x y certificate).imp (invariantAt invariant ps y)))

/-- Only single-edge acceptance is assumed. The supplied original certificate
is transformed by the already concrete edgeLift AST, at its actual graph output.
The invariant restricts the source to the intended arithmetic domain. -/
def EdgeCompatibility (body : Positive (Fin 1)) (edge : Program 3)
    (vertex invariant : Program 5) : Prop :=
  ∀ (α : Type) (ps : Parameters α) (x y certificate out other lifted : OTerm α),
  Nonempty (Derivation body []
    ((invariantAt invariant ps x ⊓
      (edgeGraph edge x y certificate ⊓
        (vertexAt vertex ps out x ⊓
          (vertexAt vertex ps other y ⊓ liftedEdgeAt ps lifted certificate)))).imp
      (edgeGraph edge out other lifted)))

def inputs {α : Type} (edge : Program 3) (vertex invariant : Program 5) (positive : Bool)
    (ps : Parameters α) (x y code out other mapped : OTerm α) : Formula α :=
  invariantAt invariant ps x ⊓
    (checkerGraph edge positive (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) x y code ⊓
      (vertexAt vertex ps out x ⊓ (vertexAt vertex ps other y ⊓ mappedAt vertex ps mapped code)))

/-- Quantify the source/target, their actual vertex outputs, and the mapped
certificate output while retaining the original map parameters and raw code. -/
def matrix {α : Type} (edge : Program 3) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) : Formula (α ⊕ Fin 5) :=
  (inputs edge vertex invariant false (fun i => (ps i).relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (code.relabel Sum.inl)
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
      (pathGraph edge (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)))

def row {α : Type} (edge : Program 3) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) : Formula α :=
  allBlock (matrix edge vertex invariant ps code)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLift
