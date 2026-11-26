import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationTargets
import LogicLineages.PersistentMarking.ProtectedSpineBoundSubstitutionProof
import LogicLineages.PersistentMarking.SpineCallTypingProof

namespace LogicLineages.PersistentMarking.ProtectedSpineConcreteInputProof
open Spine DecisionPorts NameBridge FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets
open ProtectedSpineBoundTargets
open MarkedConstructorTargets (PrefixClosed)

theorem emptyValid (E : Environment) (Γ : Context) (hw : WellFormed E.types E.ports Γ) :
    InputValid E Γ ⟨[],[]⟩ :=
  ⟨hw,by simp [ProtectedSpineEnvironmentTargets.FreeValid],
    by simp [ProtectedSpineEnvironmentTargets.BoundValid]⟩

theorem argumentTypes (σ : Ty) (args : Args) (τ : Ty) (h : CallTyped EmptyContext σ args τ) :
    BaseTyped EmptyContext args (domainTypes args) ∧ ArrowPrefix (domainTypes args) τ = σ := by
  induction h with
  | nil => exact ⟨.nil,rfl⟩
  | cons ha ht ih =>
    have hα := SpineShiftProof.annotationExact _ _ _ ha
    constructor
    · exact .cons (hα.symm ▸ ha) ih.1
    · simp only [domainTypes,MarkedConstructorTests.terms,List.map_cons,ArrowPrefix] at ih ⊢
      exact congrArg₂ Ty.arrow hα ih.2

theorem prefix (σ : Ty) (arg : Expr) (args : Args) (τ : Ty)
    (h : CallTyped EmptyContext σ (.cons arg args) τ) :
    (domainTypes (.cons arg args),τ) ∈ fullPrefixes σ :=
  (FinitePrefixProof.exactPrefix σ _ τ).mpr ⟨by simp [domainTypes,MarkedConstructorTests.terms],
    (argumentTypes σ (.cons arg args) τ h).2⟩

theorem residual (σ : Ty) (args : Args) (τ : Ty) (h : CallTyped EmptyContext σ args τ) :
    residualType σ (domainTypes args) = some τ := by
  cases args with
  | nil => cases h; rfl
  | cons a as => exact MarkedConstructorTupleProof.prefixResidual (prefix σ a as τ h)

theorem entry (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (vs : Args) (i : Nat) (v : Expr) (hv : vs.get i = some v) :
    (closedCodes S E H M Γ vs)[i]? = some (v.type,codeAt E v.type (evaluate S E H M v) Γ ⟨[],[]⟩) := by
  cases vs with
  | nil => cases hv
  | cons q qs =>
    cases i with
    | zero =>
      have h : q = v := Option.some.inj hv
      subst v
      rfl
    | succ i => exact entry S E H M Γ qs i v hv
termination_by sizeOf vs

theorem append (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (xs ys : Args) :
    closedCodes S E H M Γ (xs.append ys) =
      closedCodes S E H M Γ xs ++ closedCodes S E H M Γ ys := by
  cases xs with
  | nil => rfl
  | cons q qs =>
    change ((q.type,codeAt E q.type (evaluate S E H M q) Γ ⟨[],[]⟩) ::
      closedCodes S E H M Γ (qs.append ys)) = _
    rw [append S E H M Γ qs ys]
    rfl
termination_by sizeOf xs

theorem codeValid (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (xs : Args) (types : List Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hw : WellFormed E.types E.ports Γ) (hx : BoundImages E H xs types) :
    (closedCodes S E H M Γ xs).map Prod.fst = types ∧
    TupleValues E Γ types ((closedCodes S E H M Γ xs).map Prod.snd) := by
  have h := ProtectedSpineInterpretationProof.baseLaws S E H M hc hm EmptyContext xs types hx.1 hx.2
  exact ⟨h.types_eq Γ ⟨[],[]⟩,h.valid Γ ⟨[],[]⟩ (emptyValid E Γ hw)⟩

theorem boundValid (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (xs : Args) (types : List Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hw : WellFormed E.types E.ports Γ) (hx : BoundImages E H xs types) :
    InputValid E Γ ⟨[],closedCodes S E H M Γ xs⟩ := by
  let bs := closedCodes S E H M Γ xs
  obtain ⟨ht,hv⟩ := codeValid S E H M Γ xs types hc hm hw hx
  refine ⟨hw,by simp [ProtectedSpineEnvironmentTargets.FreeValid],?_⟩
  intro b hb
  have he : types.zip (bs.map Prod.snd) = bs := by
    rw [← ht,ProtectedSpineArgumentProof.zipProjections]
  have hb' : b ∈ types.zip (bs.map Prod.snd) := he ▸ hb
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hb'
  obtain ⟨hType,hValue⟩ := List.getElem?_zip_eq_some.mp hi
  exact hv.2 i b.1 b.2 hType hValue

theorem boundRelation (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context) (vs : Args) :
    BoundSubstitutionInputs S E H M vs [] Γ ⟨[],closedCodes S E H M Γ vs⟩ ⟨[],[]⟩ := by
  refine ⟨fun _ _ => rfl,?_ ,?_⟩
  · intro σ i hi
    simp at hi
  · intro i v hi
    have hv := entry S E H M Γ vs i v hi
    change boundCode E Γ (closedCodes S E H M Γ vs) v.type (0+i) = _
    simpa [boundCode,lookupBound,hv]

end LogicLineages.PersistentMarking.ProtectedSpineConcreteInputProof
