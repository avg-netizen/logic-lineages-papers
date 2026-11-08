module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalFixedWindowVertexDispatch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact external active-branch equality on the original numeric inputs.
Subtype closure and calibration of the original leaves suffice: canonical
typed children and valid decoded type coordinates must be DERIVED from the
selected typed tests. The existing typedApplicationCombine supplier and
original decodedApplication must be connected, not assumed as new premises.
No output canonicality or internal reflection is asserted. -/
def ActualOriginalFixedWindowActiveVertexEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCertifiedSourceGuardSelection.Calibrated n arity symbols S Gamma table data →
  ∀ (context domain codomain argument value : Nat),
  Active (OrdinaryArithmeticQuotient.contextCode symbols S table) data
    context domain codomain argument value →
  evaluate (InternalRepresentativeFoldCalibration.combine data.oldEdge)
      (List.Vector.ofFn ![domain,codomain,value,argument]) =
    ApplicationCertificateLiftPath.vertex n arity Gamma
      context domain codomain argument value

/-- ALL-input equality to the unchanged original vertex. Malformed context,
type, value and argument inputs, other windows, and failed typed guards are
included. The old calibrated Program is kept literally as the inactive branch.
Only the fixed subtype-closed selected window may use the C branch. -/
def ActualOriginalFixedWindowVertexCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : Data) (oldVertex : Program 5),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCertifiedSourceGuardSelection.Calibrated n arity symbols S Gamma table data →
  InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex →
  InternalApplicationPathMap.VertexCalibrated n arity Gamma
    (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex)

/-- Genuine internal guard factorization, under the actual original arrow
constructor graph. Arbitrary Programs, window numbers, bodies and symbolic
terms are allowed. There is no calibration or semantic-typing premise. -/
def ActualInternalFixedWindowVertexActivation : Prop :=
  ∀ (window : Nat) (data : Data) (body : Positive (Fin 1)) (α : Type)
    (context domain codomain argument value arrow : OTerm α),
  Nonempty (Derivation body []
    ((InternalApplicationCertificateConstructors.graph2 InternalListCodec.consCode arrow domain codomain).imp
      ((activationAccepted window data context domain codomain argument value).iff
        (activationFactors window data context domain argument value arrow))))

/-- Genuine internal active-branch iff for the EXACT C graph. Neither H=1,
N(value)=value, output canonicality nor any representative congruence is
imported by semantic reflection. The arbitrary inactive vertex is preserved. -/
def ActualInternalFixedWindowActiveVertexGraph : Prop :=
  ∀ (window : Nat) (data : Data) (oldVertex : Program 5)
    (body : Positive (Fin 1)) (α : Type)
    (context domain codomain argument value out : OTerm α),
  Nonempty (Derivation body []
    ((activationAccepted window data context domain codomain argument value).imp
      ((vertexGraph window data oldVertex out context domain codomain argument value).iff
        (combineGraph data out domain codomain value argument))))

/-- ONE shared original Data and ONE original five-input vertex are selected
before every body, variable type and symbolic input. Both old and dispatched
vertices satisfy the original all-input VertexCalibrated contract at fixed
Gamma. The selected guard package remains the original shared package.
This is not invariant preservation, same-edge/path compatibility, a context-
uniform compiler, outer pathValue handling or CertifiedApplicationLift. -/
def ActualOriginalFixedWindowVertexSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∃ data : Data, ∃ oldVertex : Program 5,
    InternalCertifiedSourceGuardSelection.Calibrated n arity symbols S Gamma table data ∧
      (InternalCertifiedSourceGuardSelection.SelectedCalibrated
        n arity symbols S Gamma table data ∧
        (InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex ∧
          (InternalApplicationPathMap.VertexCalibrated n arity Gamma
            (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
            ∀ (body : Positive (Fin 1)) (α : Type),
              (∀ (context domain codomain argument value arrow : OTerm α),
                Nonempty (Derivation body []
                  ((InternalApplicationCertificateConstructors.graph2 InternalListCodec.consCode arrow domain codomain).imp
                    ((activationAccepted (OrdinaryArithmeticQuotient.contextCode symbols S table)
                      data context domain codomain argument value).iff
                      (activationFactors (OrdinaryArithmeticQuotient.contextCode symbols S table)
                        data context domain argument value arrow))))) ∧
              (∀ (context domain codomain argument value out : OTerm α),
                Nonempty (Derivation body []
                  ((activationAccepted (OrdinaryArithmeticQuotient.contextCode symbols S table)
                    data context domain codomain argument value).imp
                    ((vertexGraph (OrdinaryArithmeticQuotient.contextCode symbols S table)
                      data oldVertex out context domain codomain argument value).iff
                      (combineGraph data out domain codomain value argument))))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchTargets
