module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationUniformityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRowsUniformityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedWindowEquivalence NumberedPrimarySubstitution
open OriginalHereditaryDeletionRows OriginalHereditaryObservationUniformityTargets

theorem prefixAt (Gamma : List Ty) (k : Nat) (hk : k < Gamma.length) :
    ∃ (binders tail : List Ty) (sigma : Ty), Gamma = binders ++ sigma :: tail ∧ binders.length = k := by
  induction Gamma generalizing k with
  | nil => simp at hk
  | cons sigma Gamma ih =>
    cases k with
    | zero => exact ⟨[],Gamma,sigma,rfl,rfl⟩
    | succ k =>
      obtain ⟨binders,tail,tau,he,hl⟩ := ih k (by simpa using hk)
      exact ⟨sigma::binders,tail,tau,by simp only [List.cons_append,he],by simp only [List.length_cons,hl]⟩

theorem prefixUniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) (hQ : Uniform Q n arity symbols S c)
    (binders tail : List Ty) (sigma : Ty)
    (q r : Packed (Fin n) arity (binders ++ sigma :: tail))
    (h : WindowPrimary (Fin n) arity symbols S (binders ++ sigma :: tail) q r) :
    evaluate (observation Q) (List.Vector.ofFn ![binders.length,packedNumber q,
      Nat.pair c (typesNumber (binders ++ sigma :: tail))]) =
    evaluate (observation Q) (List.Vector.ofFn ![binders.length,packedNumber r,
      Nat.pair c (typesNumber (binders ++ sigma :: tail))]) := by
  rw [← OriginalTypedDecoderReconstructionLocalProof.contextNumber,
    OriginalHereditaryDeletionRowsNativeProof.observationPrefix,
    OriginalHereditaryDeletionRowsNativeProof.observationPrefix,
    OriginalClassContextPrefixNativeProof.erasedPackedOnTyped,
    OriginalClassContextPrefixNativeProof.erasedPackedOnTyped,
    OriginalTypedDecoderReconstructionLocalProof.contextNumber]
  exact hQ (binders ++ tail) _ _
    (NumberedPrimarySubstitutionProof.actualPrimarySubstitution (Fin n) arity symbols S
      (binders ++ sigma :: tail) (binders ++ tail)
      (OriginalRawSyntaxTransport.prefixErasure binders tail sigma) q r h)

theorem cellsUniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) (hQ : Uniform Q n arity symbols S c)
    (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma)
    (h : WindowPrimary (Fin n) arity symbols S Gamma q r) (k : Nat) (hk : k < Gamma.length) :
    evaluate (observation Q) (List.Vector.ofFn ![k,packedNumber q,Nat.pair c (typesNumber Gamma)]) =
    evaluate (observation Q) (List.Vector.ofFn ![k,packedNumber r,Nat.pair c (typesNumber Gamma)]) := by
  obtain ⟨binders,tail,sigma,he,hk'⟩ := prefixAt Gamma k hk
  cases he
  rw [← hk']
  exact prefixUniform Q n arity symbols S c hQ binders tail sigma q r h

theorem lengthAtContext (Gamma : List Ty) :
    evaluate OriginalContextInsertion.length (List.Vector.ofFn ![typesNumber Gamma]) = Gamma.length := by
  rw [← OriginalTypedDecoderReconstructionLocalProof.contextNumber]
  exact OriginalContextInsertionCalibrationProof.lengthContext Gamma

theorem rowsPreserves : RowsPreserves := by
  intro Q n arity symbols S c hQ Gamma q r h
  rw [OriginalHereditaryDeletionRowsBoundProof.nativeRows,
    OriginalHereditaryDeletionRowsBoundProof.nativeRows]
  simp only [Nat.unpair_pair,lengthAtContext]
  apply congrArg NumberedMultisetNumeric.numbersNumber
  unfold values
  apply List.map_congr_left
  intro k hk
  exact cellsUniform Q n arity symbols S c hQ Gamma q r h k (List.mem_range.mp hk)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRowsUniformityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRowsUniformityProof
