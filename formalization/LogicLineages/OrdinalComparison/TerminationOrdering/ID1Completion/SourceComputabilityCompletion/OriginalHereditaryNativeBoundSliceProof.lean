module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryNativeBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryNativeBoundSliceProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence
open NumberedPrimarySubstitution OriginalHereditaryNativeBoundDefinitions
open OriginalRawSyntaxTransport (prefixErasure)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal arbitrary-prefix deletion instantiates the generic typed step;
its length drop is derived, not a premise. -/
theorem prefixDeletionStep (n : Nat) (arity : Fin n → Nat)
    (binders Gamma : List Ty) (sigma tau : Ty)
    (q : AuxTerm (Fin n) arity (binders ++ sigma :: Gamma) tau) :
    Step ⟨binders ++ sigma :: Gamma,⟨tau,q⟩⟩
      ⟨binders ++ Gamma,⟨tau,substitute q (prefixErasure binders Gamma sigma)⟩⟩ := by
  apply Step.deletion q (prefixErasure binders Gamma sigma)
  · exact OriginalClassContextPrefixNativeProof.prefixBottomOrVariable n arity binders Gamma sigma
  · simp only [List.length_append,List.length_cons]
    omega

theorem prefixDeletionSize (n : Nat) (arity : Fin n → Nat)
    (binders Gamma : List Ty) (sigma tau : Ty)
    (q : AuxTerm (Fin n) arity (binders ++ sigma :: Gamma) tau) :
    size (substitute q (prefixErasure binders Gamma sigma)) = size q :=
  OriginalHereditaryNativeBoundProof.substitutionSize q _ _
    (OriginalClassContextPrefixNativeProof.prefixBottomOrVariable n arity binders Gamma sigma)

/-- The actual context Program returns exactly the shortened context; the
native code equality is not an internal derivation or a rank estimate. -/
theorem literalDeleteContext (binders Gamma : List Ty) (sigma : Ty) :
    evaluate OriginalClassContextAllPositionObserver.deleteAt
      (List.Vector.ofFn ![binders.length,Encodable.encode (binders ++ sigma :: Gamma)]) =
      Encodable.encode (binders ++ Gamma) ∧
    (binders ++ sigma :: Gamma).length = (binders ++ Gamma).length + 1 := by
  refine ⟨OriginalClassContextAllPositionNativeSelectorsProof.deletePrefix binders Gamma sigma,?_⟩
  simp only [List.length_append,List.length_cons]
  omega

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryNativeBoundSliceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryNativeBoundSliceProof
