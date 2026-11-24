import LogicLineages.PersistentMarking.ProtectedSpineSubstitutionTargets
import LogicLineages.PersistentMarking.ProtectedSpineCoverageProof
import LogicLineages.PersistentMarking.DecisionSourceConstructProof
import LogicLineages.PersistentMarking.FreeCallProof

namespace LogicLineages.PersistentMarking.ProtectedSpineConcreteFreeCoverageProof
open Spine DecisionInventory DecisionPorts FiniteDomainSchema HereditaryDomainCode TypeSupport
open ProtectedSpineLaws ProtectedSpineSubstitutionTargets ProtectedSpineCoverageProof

mutual
  /-- Actual free images remain in the same finite types and head universe,
  including when inserted under binders. The proof uses both lists, not
  agreement only on reported output codes. -/
  theorem exact_FreeSourceCoverage (E : Environment) (H : List Head) (θ : FreeMap)
      (images : FreeImages E H θ) (q : Expr) (d : Nat) (cov : Covered E H q) :
      Covered E H (freeSub θ d q) := by
    cases q with
    | free σ x =>
      have hσ : σ ∈ E.types :=
        cov.1 _ (MarkedConstructorSourceTupleProof.rootSupport (.free σ x))
      have h := images.2 σ hσ x
      obtain ⟨hs,hh,_⟩ := DecisionSourceConstructProof.shiftFacts d 0 (θ σ x)
      exact ⟨fun t ht => h.1 t (by simpa only [freeSub,hs] using ht),
        fun f hf => h.2 f (by simpa only [freeSub,hh] using hf)⟩
    | bound σ i => exact cov
    | lam σ q =>
      have inner := exact_FreeSourceCoverage E H θ images q (d+1) (lambdaBody E H σ q cov)
      have hty := FreeCallProof.annotation θ
        (fun t x => SpineShiftProof.annotationExact _ _ _ (images.1 t x)) (d+1) q
      rcases cov with ⟨ct,ch⟩
      refine ⟨?_,inner.2⟩
      intro t ht
      simp only [freeSub,auxiliarySupport,hty,List.mem_append] at ht
      rcases ht with (h | h) | h
      · exact ct _ (by simp only [auxiliarySupport,List.mem_append]; exact Or.inl (Or.inl h))
      · exact ct _ (by simp only [auxiliarySupport,List.mem_append]; exact Or.inl (Or.inr h))
      · exact inner.1 _ h
    | head f bs =>
      have arg := exact_FreeArgumentCoverage E H θ images bs d (ordinaryBase E H f bs cov)
      constructor
      · intro t ht
        simp only [freeSub,auxiliarySupport,List.mem_append] at ht
        rcases ht with h | h
        · exact cov.1 t (by simp only [auxiliarySupport,List.mem_append]; exact Or.inl h)
        · exact arg.1 t h
      · intro u hu
        simp only [freeSub,heads,List.mem_cons] at hu
        rcases hu with h | h
        · exact cov.2 u (by simp only [heads,List.mem_cons]; exact Or.inl h)
        · exact arg.2 u h
    | marked f τ bs es =>
      have base := exact_FreeArgumentCoverage E H θ images bs d (markedBase E H f τ bs es cov)
      have extra := exact_FreeArgumentCoverage E H θ images es d (markedExtras E H f τ bs es cov)
      constructor
      · intro t ht
        simp only [freeSub,auxiliarySupport,List.mem_append] at ht
        rcases ht with ((h | h) | h) | h
        · exact cov.1 t (by simp only [auxiliarySupport,List.mem_append]; exact Or.inl (Or.inl (Or.inl h)))
        · exact cov.1 t (by simp only [auxiliarySupport,List.mem_append]; exact Or.inl (Or.inl (Or.inr h)))
        · exact base.1 t h
        · exact extra.1 t h
      · intro u hu
        simp only [freeSub,heads,List.mem_cons,List.mem_append] at hu
        rcases hu with h | h | h
        · exact cov.2 u (by simp only [heads,List.mem_cons]; exact Or.inl h)
        · exact base.2 u h
        · exact extra.2 u h
  termination_by sizeOf q
  theorem exact_FreeArgumentCoverage (E : Environment) (H : List Head) (θ : FreeMap)
      (images : FreeImages E H θ) (xs : Args) (d : Nat) (cov : ArgsCovered E H xs) :
      ArgsCovered E H (freeSubArgs θ d xs) := by
    cases xs with
    | nil => exact cov
    | cons a as =>
      obtain ⟨l,r⟩ := argumentCons E H a as cov
      have hc := exact_FreeSourceCoverage E H θ images a d l
      have hr := exact_FreeArgumentCoverage E H θ images as d r
      constructor
      · intro t ht
        rcases List.mem_append.mp ht with h | h
        · exact hc.1 t h
        · exact hr.1 t h
      · intro f hf
        rcases List.mem_append.mp hf with h | h
        · exact hc.2 f h
        · exact hr.2 f h
  termination_by sizeOf xs
end

#print axioms exact_FreeSourceCoverage
#print axioms exact_FreeArgumentCoverage
end LogicLineages.PersistentMarking.ProtectedSpineConcreteFreeCoverageProof
