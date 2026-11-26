module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source (Ty)
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm typedAt freshAt)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

/-- Use the actual chosen-a three-slot existential and a genuine scalar
carrier on the SAME given u, at the actual refined body. No carrier is
inferred merely from fresh shape. -/
def ExactGivenPackedFreshMembership : Prop :=
  ∀ (i j : Program 1) (r d : Program 3) (v : Inputs) (context : Nat)
    (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
    let S := data i j (refined i r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (freshAt (chosenA v) q u)) →
    Nonempty (Derivation B Γ (carrier S false context u)) →
    Nonempty (Derivation B Γ (membership false u))

/-- The original FreshVariablesComputable conclusion restricted only at
the requested DOMAIN to ground. The original codomain remains
arbitrary, as do the object context and the given q/u. -/
def GroundFreshAt (S : Data) (p : Program 3) (h : Program 2) (a : Program 1)
    (context : Nat) : Prop :=
  ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
    Nonempty (Derivation (sourceBody S context) Γ (typedAt h (.arrow .ground τ) q)) →
    Nonempty (Derivation (sourceBody S context) Γ (freshAt a q u)) →
    Nonempty (Derivation (sourceBody S context) Γ (formula p .ground u))

/-- Original scalar(u) is discharged by the actual reinstalled aligned
same-u tuple on the new body, not passed in as an extra premise. -/
def ExactReinstalledGroundFresh : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i j : Program 1) (r d : Program 3) (v : Inputs),
    TupleAt xs s W i j (refined i r) d v →
    ∀ context,
      GroundFreshAt (data i j (refined i r) d) v.applicationGuard (chosenH v W) (chosenA v) context

/-- The two literal concrete packets and the new-body ground-domain
proof all use one and the same originally selected p/a/h tuple. The
checked real ValidWindow premise stays explicit. -/
def ExactConcreteGroundFreshTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j : Program 1) (r d : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v ∧ TupleAt xs s W i j (refined i r) d v ∧
      ∀ context,
        GroundFreshAt (data i j (refined i r) d) v.applicationGuard (chosenH v W) (chosenA v) context

end LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTargets
