module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeNativeComparisonTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeNativeSyntaxProof
open OriginalStructuralNodeSize OriginalRawSyntaxTransport NumberedAuxiliaryCoding

theorem eraseInvariant {Symbol : Type} (q : Code Symbol) (sigma : Source.Ty) (cutoff : Nat) :
    nodeCount (eraseCode sigma cutoff q) = nodeCount q := by
  induction q generalizing cutoff with
  | var i =>
      by_cases h : i < cutoff
      · simp [eraseCode,h,nodeCount]
      · by_cases he : i = cutoff <;> simp [eraseCode,h,he,nodeCount]
  | lam tau q ih => simp only [eraseCode,nodeCount,ih]
  | app tau q a ihq iha => simp only [eraseCode,nodeCount,ihq,iha]
  | bottom tau => rfl
  | ordinary head base ih => simp only [eraseCode,nodeCount,ih]
  | numbered label head tau base types extras ihb ihe => simp only [eraseCode,nodeCount,ihb,ihe]
  | argumentsNil => rfl
  | argumentsCons tau q rest ihq ihr => simp only [eraseCode,nodeCount,ihq,ihr]

theorem sourceBound {Symbol : Type} (q : Code Symbol) :
    (NumberedSyntaxBoundsPrimrec.codeBounds q).1 ≤ nodeCount q := by
  induction q with
  | var i => exact Nat.le_refl _
  | lam tau q ih => exact Nat.add_le_add_left ih 1
  | app tau q a ihq iha => exact Nat.add_le_add (Nat.add_le_add_left ihq 1) iha
  | bottom tau => exact Nat.le_refl _
  | ordinary head base ih => exact Nat.add_le_add_left ih 1
  | numbered label head tau base types extras ihb ihe => exact Nat.add_le_add (Nat.add_le_add_left ihb 1) ihe
  | argumentsNil => exact Nat.zero_le _
  | argumentsCons tau q rest ihq ihr =>
      exact Nat.le_trans (Nat.add_le_add ihq ihr) (by omega)

theorem actualErasureInvariant : OriginalStructuralNodeSizeTargets.NativeErasureInvariant :=
  fun _ q sigma cutoff => eraseInvariant q sigma cutoff
theorem actualSourceBound : OriginalStructuralNodeSizeNativeComparisonTargets.SourceSizeBound :=
  fun _ q => sourceBound q
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeNativeSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeNativeSyntaxProof
