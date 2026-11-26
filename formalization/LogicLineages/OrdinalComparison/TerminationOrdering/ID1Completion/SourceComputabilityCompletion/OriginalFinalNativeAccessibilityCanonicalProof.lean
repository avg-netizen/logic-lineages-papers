module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformFiberProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityCanonicalProof
open Source NumberedRewriteSyntax NumberedLeastCodeRepresentative OrdinaryArithmeticQuotient
open PositiveArithmeticOperators PositiveArithmeticAccessibility
open OriginalFinalNativeAccessibility

/-- Reconstruct the original representative and discharge BOTH the rank and
positive-operator choices internally. No canonical code is omitted. -/
theorem actualOriginalCanonicalCarrierAccessibility :
    OriginalFinalNativeAccessibilityTargets.ActualOriginalCanonicalCarrierAccessibility := by
  intro n arity symbols S table hclosed htable Gamma value hvalue
  obtain ⟨rank,hrank⟩ :=
    (RankedPrecedenceCompletenessProof.actualRankCertificateExistence n table).mpr htable
  obtain ⟨scalar,multiset,hscalar⟩ :=
    PositiveArithmeticOperatorsProof.sourcePositiveOperators n arity Gamma
  obtain ⟨q,hq,he⟩ :=
    (NumberedNumericCarrierProof.canonicalCarrierTestCorrect
      n arity symbols S hclosed Gamma value).mp hvalue
  rw [← he]
  exact SourceFullSubstitutionProof.actualAllTermAccessible n arity Gamma
    (contextCode symbols S table) ((symbols,S),table) scalar
    (by simp [contextCode]) hclosed
    (fun P x => (hscalar P (contextCode symbols S table) x).1)
    rank hrank q.1 q.2 hq

/-- Accessibility lifts through the literal decoders. It does NOT assume
that arbitrary successful Object decoding is an encode/decode round trip. -/
theorem accessibleDecodedObject (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (context value : Nat)
    (ha : Acc (fun successor source =>
      PositiveArithmeticOperators.encodedR n arity Gamma context source successor) value) :
    ∀ object : Nat, Encodable.decode (α := ContextUniform.Object) object = some (Gamma,value) →
    Acc (fun successor source => ContextUniform.encodedR n arity context source successor) object := by
  induction ha with
  | intro value hacc ih =>
    intro object hobject
    refine Acc.intro object ?_
    intro successor hedge
    rcases hedge with ⟨Delta,x,y,hsource,htarget,hedge⟩
    have he : (Gamma,value) = (Delta,x) := Option.some.inj (hobject.symm.trans hsource)
    rcases Prod.mk.inj he with ⟨hGamma,hvalue⟩
    subst Delta
    subst x
    exact ih y hedge successor htarget

/-- Every original well-formed Object inherits the canonical code result,
without fixing Gamma before selecting the original relation. -/
theorem actualOriginalContextObjectAccessibility :
    OriginalFinalNativeAccessibilityTargets.ActualOriginalContextObjectAccessibility := by
  intro n arity symbols S table hclosed htable object hobject
  rcases hobject with ⟨Gamma,value,hdecode,ctx,hctx,hvalue⟩
  have hctxEq : ctx = ((symbols,S),table) := by
    simpa only [contextCode,Encodable.encodek,Option.some.injEq] using hctx.symm
  subst ctx
  exact accessibleDecodedObject n arity Gamma (contextCode symbols S table) value
    (actualOriginalCanonicalCarrierAccessibility n arity symbols S table
      hclosed htable Gamma value hvalue) object hdecode

/-- Scalar-carrier preservation at the original same-Gamma Object edges.
This supplies the carrier invariant required by standard least-model induction. -/
theorem objectScalarPreservation (n : Nat) (arity : Fin n → Nat)
    (context : Nat) (hclosed : SourceArithmeticAccessibility.DecodedSubtypeClosed n context)
    (source target : Nat) (hsource : ContextUniform.encodedScalar n arity context source)
    (hedge : ContextUniform.encodedR n arity context source target) :
    ContextUniform.encodedScalar n arity context target := by
  rcases hsource with ⟨Gamma,value,hdecode,hvalue⟩
  rcases hedge with ⟨Delta,x,y,hx,hy,hedge⟩
  have he : (Gamma,value) = (Delta,x) := Option.some.inj (hdecode.symm.trans hx)
  rcases Prod.mk.inj he with ⟨hGamma,hvalueEq⟩
  subst Delta
  subst x
  exact ⟨Gamma,y,hy,SourceArithmeticAccessibilityProof.encodedScalarPreservation
    n arity Gamma context hclosed value y hvalue hedge⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityCanonicalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityCanonicalProof
