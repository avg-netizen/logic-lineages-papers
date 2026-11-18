import LogicLineages.PersistentMarking.ProtectedSpineSoundCallSyntaxProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundLiteralProof
import LogicLineages.PersistentMarking.HereditaryCodeReconstructionProof
import LogicLineages.PersistentMarking.MarkedConstructorTupleProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundVariableProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation
open ProtectedSpineEnvironment ProtectedSpineInterpreter ProtectedSpineInterpreterCore ProtectedSpineLaws
open ProtectedSpineSoundInterpreterTargets
open ProtectedSpineSoundRelationProof (retained bottomAt)

theorem applyValue (F : Inputs S) (Γ : Context) (q : Expr) (σ : Ty) (c : Code)
    (ds : List Ty) (xs : List Code) (τ : Ty) (args : Args)
    (hw : WellFormed F.data.types F.data.ports Γ) (hr : Related F σ Γ c (some q))
    (hp : (ds,τ) ∈ fullPrefixes σ) (hx : TupleValues (domain F) Γ ds xs)
    (ht : CallTyped EmptyContext σ args τ) (hu : Sources F Γ args)
    (hs : TupleRelated F Γ ds xs args) :
    Related F τ Γ (variableCall (domain F) σ Γ c ds xs τ) (apply q args) := by
  rw [Related.eq_def] at hr
  have h := (hr.2 Γ hw (DecisionPortsProof.extensionRefl Γ)).2 ds τ hp xs args hx ht hu hs
  unfold variableCall
  rw [if_pos ⟨MarkedConstructorTupleProof.prefixResidual hp,hx.1⟩]
  exact h

theorem free (F : Inputs S) (M : Code) (σ : Ty) (x : Nat) : ExprGoal F M (.free σ x) := by
  intro Γ types vs cs _ _ hw _
  let E := domain F
  let c := literalCode E Γ σ x
  have hRel := ProtectedSpineSoundLiteralProof.literalRelated F Γ σ x hw
  constructor
  · change Related F σ Γ (encode E σ Γ (decode E σ Γ c)) (some (.free σ x))
    rw [HereditaryCodeReconstructionProof.reconstruct E σ Γ c (retained F σ Γ c _ hRel)]
    exact hRel
  · intro consumed outer _ ds τ xs args hp hx ht hu hr
    cases ds with
    | nil => exact False.elim ((FinitePrefixProof.forward _ _ _ hp).1 rfl)
    | cons d ds =>
      cases xs with
      | nil => have h := hx.1; simp at h
      | cons a xs =>
        have hApp := applyValue F Γ (.free σ x) σ c (d::ds) (a::xs) τ args hw hRel hp hx ht hu hr
        change Related F τ Γ (variableCall E σ Γ c (d::ds) (a::xs) τ) (applyAux (.free σ x) args consumed)
        rw [ProtectedSpineSoundCallSyntaxProof.closedAux (.free σ x) σ .free args consumed]
        exact hApp

theorem bound (F : Inputs S) (M : Code) (σ : Ty) (i : Nat) : ExprGoal F M (.bound σ i) := by
  intro Γ types vs cs hTyped _ hw hf
  have hi : BoundContext.prefix types EmptyContext i = some σ := by
    cases hTyped with
    | bound h => exact h
  rw [ProtectedSpineBoundSyntaxProof.emptyPrefix] at hi
  obtain ⟨v,hv,hTypedv⟩ := ProtectedSpineBoundSyntaxProof.getTyped vs types hf.1 i σ hi
  have hAnn := SpineShiftProof.annotationExact _ _ _ hTypedv
  have hRel : Related F σ Γ (boundCode (domain F) Γ cs σ i) (some v) :=
    hAnn ▸ ProtectedSpineSoundFrameProof.lookup F Γ hf.2.2 i v hv
  let E := domain F
  let c := boundCode E Γ cs σ i
  constructor
  · have hSub : substitute vs 0 (.bound σ i) = v := by
      simp [substitute,hv,SubstitutionProof.shiftZero]
    change Related F σ Γ (encode E σ Γ (decode E σ Γ c)) (some (substitute vs 0 (.bound σ i)))
    rw [hSub,HereditaryCodeReconstructionProof.reconstruct E σ Γ c (retained F σ Γ c _ hRel)]
    exact hRel
  · intro consumed outer hEq ds τ xs args hp hx ht hu hr
    cases ds with
    | nil => exact False.elim ((FinitePrefixProof.forward _ _ _ hp).1 rfl)
    | cons d ds =>
      cases xs with
      | nil => have h := hx.1; simp at h
      | cons a xs =>
        change Related F τ Γ
          (if protectedLookup consumed.length i then StructuralActions.bottom E τ Γ
            else variableCall E σ Γ c (d::ds) (a::xs) τ)
          (applyAux (substitute outer consumed.length (.bound σ i)) args consumed)
        by_cases hk : i < consumed.length
        · simp only [protectedLookup,decide_eq_true hk,if_true]
          exact bottomAt F τ Γ _ hw
        · have hOuter : outer.get (i-consumed.length) = some v := by
            rw [hEq,RefinementFreeBlockProof.appendGet,if_neg hk] at hv
            exact hv
          have hSub : substitute outer consumed.length (.bound σ i) = v := by
            simp [substitute,hk,hOuter,ClosedSyntaxProof.closedShift v σ hTypedv consumed.length]
          rw [hSub,ProtectedSpineSoundCallSyntaxProof.closedAux v σ hTypedv args consumed]
          simp only [protectedLookup,decide_eq_false hk,if_false]
          exact applyValue F Γ v σ c (d::ds) (a::xs) τ args hw hRel hp hx ht hu hr

end LogicLineages.PersistentMarking.ProtectedSpineSoundVariableProof
