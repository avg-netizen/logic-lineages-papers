module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalTypedEdgePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The additional membership guard preserves the ENTIRE original canonical
typed zero/one function on all natural [value,type] pairs and arbitrary S.
No subtype closure or successful typed/decoded input is assumed. The proof
must derive root-type membership from the unchanged original universe test. -/
def ActualOriginalMembershipTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (validity : InternalOriginalStepGuard.Data) (member : Program 1) (oldTyped : Program 2),
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity →
  InternalStructuralEndpointGuard.MembershipCalibrated S member →
  InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma oldTyped →
  InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma
    (typedChecker validity member oldTyped)

/-- ONE calibrated leaf selection and its explicit ASTs precede every type,
predicate body and symbolic input. All external calibrations cover arbitrary
windows and every natural input. On a subtype-closed window, the original
internal calculus derives the actual endpoint and raw-tag graphs from only
typed source, typed argument, selectors and accepted quotient edge.

There is no target-typed, raw-validity, raw-tag, codomain-membership, endpoint-
acceptance or lift premise. Closed type-code evaluations may use the checked
original numeral-evaluation theorem; external calibration is not an internal
inference rule on symbolic values. This is an endpoint presentation, not
application-validity closure, representative congruence or a certified lift. -/
def ActualOriginalTypedEdgePresentation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  ∃ data : Data,
    Calibrated n arity symbols S Gamma table data ∧
      (PresentationCalibrated n arity symbols S Gamma table data ∧
        (SubtypeClosed (fun typ => typ ∈ S) →
          ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type)
            (x y a certificate s t k : OTerm α),
          Nonempty (Derivation body []
            ((premises data sigma tau x y a certificate s t k).imp
              (requirements data sigma tau s t a)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationTargets
