import LogicLineages.PersistentMarking.ProtectedSpineEncodingProof
import LogicLineages.PersistentMarking.StructuralFullActionProof
import LogicLineages.PersistentMarking.MarkedConstructorTupleProof

namespace LogicLineages.PersistentMarking.ProtectedSpineVariableProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode
open HereditaryDomainSemantics ProtectedSpineEnvironment ProtectedSpineInterpreterCore ProtectedSpineLaws

def lookupEvaluation (E : Environment) (σ : Ty) (get : Context → Assignments → Code)
    (blocked : Nat → Bool) : Evaluation where
  value Γ free bound := decode E σ Γ (get Γ ⟨free,bound⟩)
  nonempty Γ free bound k d x ds xs τ :=
    if blocked k then StructuralActions.bottom E τ Γ
    else variableCall E σ Γ (get Γ ⟨free,bound⟩) (d::ds) (x::xs) τ

theorem callEq (E : Environment) (σ : Ty) (get : Context → Assignments → Code)
    (blocked : Nat → Bool) (Γ : Context) (a : Assignments) (k : Nat) (ds : List Ty) (τ : Ty)
    (xs : List Code) (hpre : (ds,τ) ∈ fullPrefixes σ) (hx : TupleValues E Γ ds xs) :
    nonemptyAt E (lookupEvaluation E σ get blocked) Γ a k ds τ xs =
      if blocked k then StructuralActions.bottom E τ Γ
      else StructuralActions.fullAction E σ Γ (get Γ a) ds τ xs := by
  have hres := MarkedConstructorTupleProof.prefixResidual hpre
  cases ds with
  | nil => exact False.elim ((FinitePrefixProof.forward σ [] τ hpre).1 rfl)
  | cons d ds =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      change (if blocked k then _ else variableCall E σ Γ (get Γ ⟨a.free,a.bound⟩) (d::ds) (x::xs) τ) = _
      cases a
      simp [variableCall,hres,hx.1]

theorem laws (E : Environment) (σ : Ty) (get : Context → Assignments → Code) (blocked : Nat → Bool)
    (hvalid : ∀ Γ a, InputValid E Γ a → get Γ a ∈ (descriptor E σ).carriers Γ)
    (hnatural : ∀ Γ Δ a, InputValid E Γ a → WellFormed E.types E.ports Δ → Extends Γ Δ →
      (descriptor E σ).restrict Γ Δ (get Γ a) = get Δ (a.restrict E Γ Δ))
    (horder : ∀ Γ a b, InputLE E Γ a b → (descriptor E σ).le Γ (get Γ a) (get Γ b) = true) :
    EvaluationLaws E σ (lookupEvaluation E σ get blocked) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro Γ a ha
    cases a
    exact HereditaryDecodedValidityProof.valid E σ Γ _ ha.1 (hvalid Γ _ ha)
  · intro Γ Δ a ha hd he
    have hr := (HereditaryRestrictionProof.restriction E σ Γ Δ ha.1 hd he _ (hvalid Γ a ha)).2
    rw [hnatural Γ Δ a ha hd he] at hr
    cases a
    exact HereditaryValueEqualityProof.symm hr
  · intro Γ a b ha hb hab
    have h := (HereditaryCodeOrderProof.exactOrder E σ Γ _ _ ha.1
      (hvalid Γ a ha) (hvalid Γ b hb)).mp (horder Γ a b hab)
    cases a
    cases b
    exact h
  · intro Γ a k ds τ xs ha hpre hx
    rw [callEq E σ get blocked Γ a k ds τ xs hpre hx]
    cases blocked k
    · exact StructuralFullActionProof.sound E σ Γ _ ds τ xs ha.1 (hvalid Γ a ha) hpre hx
    · exact (StructuralWholeBottomProof.wholeBottom E τ Γ ha.1).1
  · intro Γ Δ a k ds τ xs ha hd he hpre hx
    have hx' : TupleValues E Δ ds (restrictValues E Γ Δ ds xs) :=
      MarkedBaseTupleRestrictionProof.restriction E Γ Δ ds xs ha.1 hd he hx
    rw [callEq E σ get blocked Γ a k ds τ xs hpre hx,
      callEq E σ get blocked Δ (a.restrict E Γ Δ) k ds τ _ hpre hx']
    cases blocked k
    · have h := StructuralFullActionProof.natural E σ Γ Δ _ ds τ xs ha.1 hd he (hvalid Γ a ha) hpre hx
      rw [hnatural Γ Δ a ha hd he] at h
      exact h
    · exact ProtectedSpineEnvironmentNaturalProof.bottomNatural E τ Γ Δ ha.1 hd he
  · intro Γ a b k ds τ xs ys ha hb hab hpre hx hy hxy
    rw [callEq E σ get blocked Γ a k ds τ xs hpre hx,callEq E σ get blocked Γ b k ds τ ys hpre hy]
    cases blocked k
    · exact StructuralFullActionProof.monotone E σ Γ _ _ ds τ xs ys ha.1 (hvalid Γ a ha) (hvalid Γ b hb)
        (horder Γ a b hab) hpre hx hy hxy
    · exact (HereditaryPartialOrderProof.partialOrder E τ Γ ha.1).1 _
        (StructuralWholeBottomProof.wholeBottom E τ Γ ha.1).1

theorem free (S : Signature) (E : Environment) (heads : List Head) (M : Code) (σ : Ty) (x : Nat) :
    EvaluationLaws E σ (ProtectedSpineInterpreter.evaluate S E heads M (.free σ x)) :=
  laws E σ (fun Γ a => freeCode E Γ a.free σ x) (fun _ => false)
    (fun Γ a ha => ProtectedSpineEnvironmentLookupProof.freeLookup E Γ a.free σ x ha.1 ha.2.1)
    (fun Γ Δ a ha hd he => (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ x 0 ha.1 hd he ha.2.1 ha.2.2).1)
    (fun _ _ _ hab => hab.1 σ x)

theorem bound (S : Signature) (E : Environment) (heads : List Head) (M : Code) (σ : Ty) (i : Nat) :
    EvaluationLaws E σ (ProtectedSpineInterpreter.evaluate S E heads M (.bound σ i)) :=
  laws E σ (fun Γ a => boundCode E Γ a.bound σ i) (fun k => protectedLookup k i)
    (fun Γ a ha => ProtectedSpineEnvironmentLookupProof.boundLookup E Γ a.bound σ i ha.1 ha.2.2)
    (fun Γ Δ a ha hd he => (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ 0 i ha.1 hd he ha.2.1 ha.2.2).2)
    (fun _ _ _ hab => hab.2 σ i)

end LogicLineages.PersistentMarking.ProtectedSpineVariableProof
