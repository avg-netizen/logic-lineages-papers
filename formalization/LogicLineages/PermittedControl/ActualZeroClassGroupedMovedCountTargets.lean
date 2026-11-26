module
public import LogicLineages.PermittedControl.ActualCountOriginDispositionsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassGroupedMovedCount
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualRankedRowColumns
open ActualZeroClassCohortTransfer ActualCountOriginDispositions

/-- Match the actual anchor to its literal finite rank and canonical prefix
label. With no surviving anchor the finite arguments serve only as dummy
indices: all dispositions that are actually realized are ended. -/
def AnchorAt {r : Nat} (anchor : Option SurvivingPrefix) (x₀ : Fin r)
    (q : NONote × NONote) : Prop :=
  ∀ a, anchor = some a → a.rank = x₀.val ∧ (a.lam,a.eta) = q

/-- The original ordered ledger's signed terms, added as actual Finsupp
columns. Distinct original keys may emit the same lowered key; its weights
are added here rather than selecting only one occurrence. -/
noncomputable def movedCountTerms {r : Nat} (x₀ : Fin r) (q : NONote × NONote)
    (ledger : List (Origin × CountDisposition)) : CountKey r →₀ Int :=
  (ledger.map (fun pair => pair.2.term x₀ q pair.1.1.1.1)).sum

/-- The exact count column of the actual moved reads emitted by the
selected zero-class origin ledger. This does not yet turn an ordered
ledger into the Finset-summed replacement relation for a whole row. -/
def ExactGroupedMovedCount : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (xs : List Read)
    (annotations : List Annotation) (anchor : Option SurvivingPrefix) (x₀ : Fin r)
    (q : NONote × NONote) (ledger : List (Origin × CountDisposition)) (moved : List Read),
    AnchorAt anchor x₀ q →
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved →
    (rankedRow r 0 moved).count = movedCountTerms x₀ q ledger

end LogicLineages.PermittedControl.ActualZeroClassGroupedMovedCount
