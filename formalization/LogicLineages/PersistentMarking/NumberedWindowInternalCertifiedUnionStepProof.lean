module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus
open ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm)
open ID1Completion.InternalAccessibilityRulesProof
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectSourcePartitionRawTargets (rawSourceCheck observePartition sourceTape)
open NumberedWindowInternalDirectCoreNumericTargets (CountFit)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

/-- The literal packed-union observation: all three original field codes
parse, the two parsed components are appended in order, and the supplied
count observer accepts the result against the parsed original union code. -/
def unionGraph {α : Type} (count : Program 2) (a b u : OTerm α) : Formula α :=
  programGraph (rawSourceCheck (observePartition count)) (suc z) (sourceTape u a b)

abbrev Pr {α : Type} (data : Data) (c : Nat) (Γ : List (Formula α)) (f : Formula α) : Prop :=
  Nonempty (Derivation (sourceBody data c) Γ f)

/-- Continuations for an origin-labelled split. Each changed component has
its own original certificate. An unchanged component is the very same term,
and the recombination is at the very same original successor target. -/
structure SplitCases (data : Data) (c : Nat) (count : Program 2)
    {α : Type} (Γ : List (Formula α)) (a b v : OTerm α) (goal : Formula α) : Prop where
  leftOnly : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a' wa : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Pr data c Δ (certificate data true c (a.relabel j) a' wa) →
    Pr data c Δ (unionGraph count a' (b.relabel j) (v.relabel j)) →
    Pr data c Δ (goal.relabel j)
  rightOnly : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (b' wb : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Pr data c Δ (certificate data true c (b.relabel j) b' wb) →
    Pr data c Δ (unionGraph count (a.relabel j) b' (v.relabel j)) →
    Pr data c Δ (goal.relabel j)
  both : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a' b' wa wb : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Pr data c Δ (certificate data true c (a.relabel j) a' wa) →
    Pr data c Δ (certificate data true c (b.relabel j) b' wb) →
    Pr data c Δ (unionGraph count a' b' (v.relabel j)) →
    Pr data c Δ (goal.relabel j)

/-- The explicitly unpaid arithmetic split. It eliminates an actual
certificate for arbitrary goals, not just J, and must rebuild the exact
original certificates and packed-union report in a branch. -/
def CertifiedOriginSplit (data : Data) (c : Nat) (count : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (a b u v w : OTerm α) (goal : Formula α),
    Pr data c Γ (carrier data true c u) →
    Pr data c Γ (unionGraph count a b u) →
    Pr data c Γ (certificate data true c u v w) →
    SplitCases data c count Γ a b v goal →
    Pr data c Γ goal

/-- Already-held outer lower cases, restricted to actual strict edges of
the original left component, and the genuine right membership and report. -/
def HeldOuter (data : Data) (c : Nat) (count : Program 2)
    {α : Type} (Γ : List (Formula α)) (a : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a' b' v' : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Pr data c Δ (edge data true c (a.relabel j) a') →
    Pr data c Δ (membership true b') →
    Pr data c Δ (unionGraph count a' b' v') →
    Pr data c Δ (membership true v')

/-- Already-held inner lower cases, restricted to actual strict edges of
the original right component, with the left component unchanged. -/
def HeldInner (data : Data) (c : Nat) (count : Program 2)
    {α : Type} (Γ : List (Formula α)) (a b : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (b' v' : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Pr data c Δ (edge data true c (b.relabel j) b') →
    Pr data c Δ (unionGraph count (a.relabel j) b' v') →
    Pr data c Δ (membership true v')

def ExactOriginalCertifiedUnionStep : Prop :=
  ∀ (data : Data) (c : Nat) (count : Program 2),
    CountFit count →
    CertifiedOriginSplit data c count →
    ∀ (α : Type) (Γ : List (Formula α)) (a b u v w : OTerm α),
      HeldOuter data c count Γ a →
      HeldInner data c count Γ a b →
      Pr data c Γ (membership true b) →
      Pr data c Γ (carrier data true c u) →
      Pr data c Γ (unionGraph count a b u) →
      Pr data c Γ (certificate data true c u v w) →
      Pr data c Γ (membership true v)

/-- Only this one original certified union successor is discharged. The
nested construction of the held induction hypotheses is separate. -/
theorem exact_OriginalCertifiedUnionStep : ExactOriginalCertifiedUnionStep := by
  intro data c count _countFit split α Γ a b u v w outer inner hb carrierU joined step
  have keepRight (β : Type) (j : α → β) (Δ : List (Formula β))
      (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
      Pr data c Δ (membership true (b.relabel j)) := by
    have carried := renameInto hb j Δ keep
    rw [membershipRename] at carried
    exact carried
  apply split α Γ a b u v w (membership true v) carrierU joined step
  constructor
  · intro β j Δ a' wa keep ha hu
    rw [membershipRename]
    exact outer β j Δ a' (b.relabel j) (v.relabel j) keep
      (edgeIntroduction ha) (keepRight β j Δ keep) hu
  · intro β j Δ b' wb keep hr hu
    rw [membershipRename]
    exact inner β j Δ b' (v.relabel j) keep (edgeIntroduction hr) hu
  · intro β j Δ a' b' wa wb keep ha hr hu
    rw [membershipRename]
    have lowerRight := actualOriginalCertifiedSuccessorClosure
      data true c β Δ (b.relabel j) b' wb (keepRight β j Δ keep) hr
    exact outer β j Δ a' b' (v.relabel j) keep (edgeIntroduction ha) lowerRight hu

#print axioms exact_OriginalCertifiedUnionStep

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
