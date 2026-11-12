module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionTargets
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding
open OriginalRawSyntaxTransport OriginalTwoDeletion
/-- Native syntax identity, including all eight original constructors.
The earlier cutoff is i; the later cutoff j shifts down after deleting i. -/
def RawCommutation : Prop :=
  ∀ (Symbol : Type) (alpha beta : Ty) (i j : Nat), i < j → ∀ q : Code Symbol,
  eraseCode alpha i (eraseCode beta j q) = eraseCode beta (j - 1) (eraseCode alpha i q)
/-- Equality of actual ORIGINAL typed terms in the common final context,
not merely a rank/key observation. Lambda lifting is part of substitution;
BASE/extras remain their original constructors. No canonical claim. -/
def TypedCommutation : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (A B Gamma : List Ty) (alpha beta tau : Ty)
    (q : AuxTerm Symbol arity (A ++ alpha :: (B ++ beta :: Gamma)) tau),
  lowerFirst A B Gamma alpha beta tau q = upperFirst A B Gamma alpha beta tau q
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionTargets
