module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipTargets
open Source InternalOriginalUniformContextMembership
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every raw parameter and type is included. The original Object codec is
total, so membership depends only on the original context coordinate even
though memberValue is expressed through the shared decoded-value wrapper. -/
def ActualOriginalUniformMembershipParameterIndependence : Prop :=
  ∀ (n typ parameter : Nat),
    InternalOriginalUniformParameterLeaves.memberValue n (List.Vector.ofFn ![typ,parameter]) =
      InternalOriginalUniformParameterLeaves.memberValue n
        (List.Vector.ofFn ![typ,Nat.pair (Nat.unpair parameter).1 0])

/-- Preserve the full all-input four-leaf contract, including malformed
context codes. Only the membership AST changes by the displayed composition;
no source, target, representative or decoder contract is weakened. -/
def ActualOriginalUniformNormalizedMembershipCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
    InternalOriginalUniformDescentSelection.Calibrated n arity data →
    InternalOriginalUniformDescentSelection.Calibrated n arity (normalizeData data)

/-- The concrete normalized AST has the symbolic slice law for every
original binary member, body and context. No external calibration or truth
reflection is a premise; original pair inversion supplies the left field. -/
def ActualOriginalUniformMembershipSlice : Prop :=
  ∀ member : Program 2, SliceLaw member

/-- Select the original tuple once and apply the fixed syntactic
normalization before every source window, Gamma, arithmetic body and term.
The normalized tuple has global calibration, both previously proved internal
law packages, the exact symbolic membership slice, and all original descent,
typed, canonical-fold and whole-state-success calibrations. No fixed-Gamma
premise, new source codec or certified application-lift conclusion is added. -/
def ActualOriginalUniformNormalizedMembershipSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ data : Data,
    InternalOriginalUniformDescentSelection.Calibrated n arity data ∧
    InternalOriginalUniformDescentSelection.Calibrated n arity (normalizeData data) ∧
    InternalOriginalUniformDescentSelection.InternalLaws (normalizeData data) ∧
    InternalParameterizedCanonicalResultFold.InternalLaws (normalizeData data) ∧
    SliceLaw data.member ∧
    ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
      SubtypeClosed (fun tau => tau ∈ S) →
      InternalOriginalUniformCanonicalResultFold.SelectedCalibrated
        n arity symbols S Gamma table (normalizeData data)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipTargets
