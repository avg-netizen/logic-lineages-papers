module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembership
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [type,context]. The original binary membership AST receives the
unchanged type and the original pair code of context with zero. This is a
concrete AST composition, not an extensional replacement of its graph. -/
def contextMember (member : Program 2) : Program 2 :=
  .composition member
    ![.projection 0,pairOf (.projection 1) (InternalAcceptance.constantZero 2)]

/-- Inputs [type,parameter]. Only the actual left selector of the parameter
feeds contextMember. No Gamma validity or successful-decoding test is added. -/
def normalizedMember (member : Program 2) : Program 2 :=
  .composition (contextMember member) ![.projection 0,leftOf (.projection 1)]

/-- Replace precisely the membership field. All three original validity
and representative leaves remain the identical Program ASTs. -/
def normalizeData (data : Data) : Data :=
  { data with member := normalizedMember data.member }

/-- Internal symbolic slice at an ACTUAL original pair graph. The original
parameter and Gamma code may be arbitrary terms, including malformed codes.
The output is arbitrary, not restricted to acceptance one. -/
def SliceLaw (member : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (out typ parameter context gammaCode : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing parameter context gammaCode).imp
      ((graph2 (normalizedMember member) out typ parameter).iff
        (graph2 (contextMember member) out typ context))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembership
