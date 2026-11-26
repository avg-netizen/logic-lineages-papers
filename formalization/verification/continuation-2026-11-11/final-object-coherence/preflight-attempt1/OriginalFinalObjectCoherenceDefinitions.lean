module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherence
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedFiniteUniverse OriginalRawObjectTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Bookkeeping wrapper around the literal SAME final fold. The actual
encoded context is retained and paired with the same outer context parameter.
This is not a new selector or an alternative canonical Data tuple. -/
def canonicalObject (p : GlobalSourcePackage.Inputs) (context input : Nat) : Nat :=
  Nat.pair (Nat.unpair input).1
    (evaluate (InternalParameterizedCanonicalResultFold.foldN
      (OriginalLambdaTraversalSelection.finalData p))
      (List.Vector.ofFn ![(Nat.unpair input).2,Nat.pair context (Nat.unpair input).1]))

/-- Native cancellation across the ACTUAL SAME final canonical fold at both
runtime contexts. The added context type need not belong to the window.
Primary equivalence is not interpreted as a strict reduction certificate. -/
def Cancellation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → ∀ (sigma tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma tau),
  InUniverse symbols S q →
  let K := canonicalObject p (OrdinaryArithmeticQuotient.contextCode symbols S table)
  let X := ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩)
  K (evaluate eraseObjectRaw (List.Vector.ofFn ![
    K (evaluate shiftObjectRaw (List.Vector.ofFn ![typeNumber sigma,X]))])) = K X

/-- The original all-variable-occurrence rank is unchanged by this SAME
final fold on original typed source-universe inputs. Native only. -/
def RankInvariance (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → ∀ (tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma tau),
  InUniverse symbols S q →
  let K := canonicalObject p (OrdinaryArithmeticQuotient.contextCode symbols S table)
  let X := ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩)
  evaluate variableRankObjectRaw (List.Vector.ofFn ![K X]) =
    evaluate variableRankObjectRaw (List.Vector.ofFn ![X])

/-- The complete previous global Package and SAME-final laws coexist with
the two native Object consequences at the IDENTICAL original input tuple p.
No internal Object coherence or C/I transport is asserted. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  OriginalLambdaTraversalSelection.Properties n arity p ∧
    Cancellation n arity p ∧ RankInvariance n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherence
