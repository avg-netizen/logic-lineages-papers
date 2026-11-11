module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrence
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open OriginalHereditaryValidity

/-- Native structural descendants of the EXACT raw root frame. Only literal
application tag two and lambda tag one descend. Every application child keeps
its parent's parameter; every lambda body uses the actual domain field and
the original successor/pair Gamma extension. This is not a new source set or
an assumed recurrence for the bounded validator. -/
inductive DescendantFrame (root : Frame) : Frame → Prop
  | root : DescendantFrame root root
  | function {frame : Frame} :
      DescendantFrame root frame → tagValue frame.raw = 2 →
      DescendantFrame root ⟨functionChildValue frame.raw, frame.parameter⟩
  | argument {frame : Frame} :
      DescendantFrame root frame → tagValue frame.raw = 2 →
      DescendantFrame root ⟨argumentChildValue frame.raw, frame.parameter⟩
  | body {frame : Frame} :
      DescendantFrame root frame → tagValue frame.raw = 1 →
      DescendantFrame root
        ⟨lambdaBodyValue frame.raw, childParameterValue frame.raw frame.parameter⟩

/-- A native typed-window invariant using the ORIGINAL packed term and Object
Gamma encodings. The raw outer context is retained literally, even if it is
not a preferred encoding of its decoded Context. Every visited term has its
own actual Gamma and all original universe guards. No subtype-closure or
finite-window validity premise is built into this predicate. -/
def TypedWindowFrame (n : Nat) (arity : Fin n → Nat)
    (context : Nat) (frame : Frame) : Prop :=
  ∃ ctx : OrdinaryArithmeticQuotient.Context n,
    Encodable.decode context = some ctx ∧
    ∃ Gamma : List Ty,
      frame.parameter = Nat.pair context (Encodable.encode Gamma) ∧
      ∃ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
        frame.raw = packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma) ∧
          tau ∈ ctx.1.2 ∧ NumberedFiniteUniverse.InUniverse ctx.1.1 ctx.1.2 q

/- NATIVE RECURRENCE PACKET ONLY. The validator, fuel, transition, initial
state, guard, normalizedData and refineData are the unchanged definitions in
OriginalHereditaryValidity. In particular, normalizedData rawData is exactly
normalizeData (BottomParameter.baseData rawData), guard captures those three
normalized leaves, and refineData conjoins the guard with the RAW oldSource.

These definitions do not provide internal graph consequences. Internal
bottom-parameter invariance of this hereditary guard, lambda-body closure at
the SAME eventual source Program, and retention of the complete final Package
remain separate pending obligations. Numeric calibration is not an internal
inference rule. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrence
