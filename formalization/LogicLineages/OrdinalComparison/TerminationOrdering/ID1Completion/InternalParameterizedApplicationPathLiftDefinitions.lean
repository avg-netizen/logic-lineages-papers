module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLift
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalParameterizedPathChecker InternalClosedPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The existing map's parameter tuple is reused verbatim. Its old context
slot now carries p, giving [parameter,domain,codomain,RAWargument]. -/
abbrev Parameters (α : Type) := InternalApplicationPathLift.Parameters α

abbrev vertexInputs {α : Type} (ps : Parameters α) (x : OTerm α) : Fin 5 → OTerm α :=
  InternalApplicationPathLift.vertexInputs ps x

/-- Exact old vertex input order [parameter,domain,codomain,RAWargument,value]. -/
abbrev vertexAt {α : Type} (vertex : Program 5) (ps : Parameters α) (out x : OTerm α) : Formula α :=
  InternalApplicationPathLift.vertexAt vertex ps out x

abbrev invariantAt {α : Type} (invariant : Program 5) (ps : Parameters α) (x : OTerm α) : Formula α :=
  InternalApplicationPathLift.invariantAt invariant ps x

/-- The original edgeLift uses the unchanged domain, codomain, RAWargument
and edge certificate. The parameter is not added to this source encoding. -/
abbrev liftedEdgeAt {α : Type} (ps : Parameters α) (out certificate : OTerm α) : Formula α :=
  InternalApplicationPathLift.liftedEdgeAt ps out certificate

/-- The old concrete pathMap AST, with inputs [code,parameter,domain,
codomain,RAWargument]. No new mapper, certificate representation or fuel. -/
abbrev mappedAt {α : Type} (vertex : Program 5) (ps : Parameters α) (out code : OTerm α) : Formula α :=
  InternalApplicationPathLift.mappedAt vertex ps out code

/-- An internal single-edge arithmetic invariant rule at the same p.
Path closure and computability are not included as assumptions. -/
def InvariantPreservation (body : Positive (Fin 1)) (edge : Program 4) (invariant : Program 5) : Prop :=
  ∀ (α : Type) (ps : Parameters α) (x y certificate : OTerm α),
  Nonempty (Derivation body []
    ((invariantAt invariant ps x ⊓ edgeGraph edge x y certificate (ps 0)).imp
      (invariantAt invariant ps y)))

/-- Only one original edge is lifted. Both actual vertex outputs and the
actual edgeLift output are retained, and all edge calls receive identical p. -/
def EdgeCompatibility (body : Positive (Fin 1)) (edge : Program 4)
    (vertex invariant : Program 5) : Prop :=
  ∀ (α : Type) (ps : Parameters α) (x y certificate out other lifted : OTerm α),
  Nonempty (Derivation body []
    ((invariantAt invariant ps x ⊓
      (edgeGraph edge x y certificate (ps 0) ⊓
        (vertexAt vertex ps out x ⊓
          (vertexAt vertex ps other y ⊓ liftedEdgeAt ps lifted certificate)))).imp
      (edgeGraph edge out other lifted (ps 0))))

def inputs {α : Type} (edge : Program 4) (vertex invariant : Program 5) (positive : Bool)
    (ps : Parameters α) (x y code out other mapped : OTerm α) : Formula α :=
  invariantAt invariant ps x ⊓
    (checkerGraph edge positive (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
        x y code (ps 0) ⊓
      (vertexAt vertex ps out x ⊓ (vertexAt vertex ps other y ⊓ mappedAt vertex ps mapped code)))

/-- The same five endpoints/output coordinates vary inside the list-code
induction row. Every free map parameter, including p, is relabeled under it. -/
def matrix {α : Type} (edge : Program 4) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) : Formula (α ⊕ Fin 5) :=
  (inputs edge vertex invariant false (fun i => (ps i).relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (code.relabel Sum.inl)
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
      (pathGraph edge (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) ((ps 0).relabel Sum.inl))

def row {α : Type} (edge : Program 4) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) : Formula α :=
  allBlock (matrix edge vertex invariant ps code)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLift
