module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalAccessibilityRules

/-- Both actual accessibility slices, in the original joint-context calculus.
The successor relation is the unchanged original arithmetic certificate graph. -/
def ActualOriginalMembershipEquation : Prop :=
  ∀ (data : SourcePresentation.Data) (odd : Bool) (context : Nat) (α : Type)
    (x : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((membership odd x).iff (carrier data odd context x ⊓ successors data odd context x)))

def ActualOriginalCarrierExtraction : Prop :=
  ∀ (data : SourcePresentation.Data) (odd : Bool) (context : Nat) (α : Type)
    (Gamma : List (Formula α)) (x : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (membership odd x)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (carrier data odd context x))

/-- Internal downward closure under R for I and under DM(R) for J.
The endpoints remain arbitrary arithmetic terms, not closed numeral instances. -/
def ActualOriginalSuccessorClosure : Prop :=
  ∀ (data : SourcePresentation.Data) (odd : Bool) (context : Nat) (α : Type)
    (Gamma : List (Formula α)) (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (membership odd x)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (edge data odd context x y)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (membership odd y))

/-- The same closure from an explicitly supplied original certificate graph. -/
def ActualOriginalCertifiedSuccessorClosure : Prop :=
  ∀ (data : SourcePresentation.Data) (odd : Bool) (context : Nat) (α : Type)
    (Gamma : List (Formula α)) (x y witness : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (membership odd x)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma
    (certificate data odd context x y witness)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (membership odd y))

/-- The actual source closure rule retains all typedness and successor premises. -/
def ActualOriginalAccessibilityIntroduction : Prop :=
  ∀ (data : SourcePresentation.Data) (odd : Bool) (context : Nat) (α : Type)
    (Gamma : List (Formula α)) (x : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (carrier data odd context x)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (successors data odd context x)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (membership odd x))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesTargets
