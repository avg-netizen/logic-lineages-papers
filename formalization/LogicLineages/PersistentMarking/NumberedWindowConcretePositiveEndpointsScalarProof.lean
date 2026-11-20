module
public import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsTargets
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsWalkProof
import LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationChecks
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsScalarProof
open NumberedWindowConcretePositiveEndpointsTargets
open NumberedWindowConcretePositiveEndpointsWalkProof (boundaryHops)
open NumberedWindowRawClassSaturationChecks (exact_RawLeastClosureWithVertices)
open NumberedWindowRawExchangeVerticesChecks (exact_OriginalGuardedEdgeVertices)
open NumberedWindowScalarAlgorithm (scalar canonical)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowPositivePathAlgorithm (addressRS)
open NumberedWindowConcreteCheckers (step positive)

theorem rawEndpoints : ExactConcretePositiveRawEndpoints := by
  intro entries s ctx ty source witness target ok
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,firstHop,lastHop⟩ :=
    boundaryHops entries s ctx ty source witness target ok
  obtain ⟨q,_,_,_,_,qAdmitted,_,startLeast,_⟩ := firstHop
  obtain ⟨_,_,r,_,_,_,rAdmitted,_,endLeast⟩ := lastHop
  have closes := exact_RawLeastClosureWithVertices s ctx ty (exact_OriginalGuardedEdgeVertices s ctx ty)
  have start := closes q source qAdmitted startLeast
  have finish := closes r target rAdmitted endLeast
  exact ⟨start.2.1,start.2.2,finish.2.1,finish.2.2⟩

theorem scalarEndpoints : ExactConcretePositiveScalarEndpoints := by
  intro entries s x witness y ok
  change addressRS (step entries s) (NumberedWindowScalarAlgorithm.least s) x witness y = true at ok
  unfold addressRS at ok
  cases sourceView : addressView x with
  | none => simp [sourceView] at ok
  | some source =>
    rcases source with ⟨sourceCtx,sourceTy,sourceRaw⟩
    cases targetView : addressView y with
    | none => simp [sourceView,targetView] at ok
    | some target =>
      rcases target with ⟨targetCtx,targetTy,targetRaw⟩
      have reports : sourceCtx = targetCtx ∧ sourceTy = targetTy ∧
          NumberedWindowPositivePathAlgorithm.positive (step entries s)
            (NumberedWindowScalarAlgorithm.least s) sourceCtx sourceTy sourceRaw witness targetRaw =
              true := by
        simpa [sourceView,targetView,Bool.and_eq_true,beq_iff_eq,and_assoc] using ok
      obtain ⟨sameCtx,sameTy,accepted⟩ := reports
      subst targetCtx
      subst targetTy
      obtain ⟨sourceAdmitted,sourceLeast,targetAdmitted,targetLeast⟩ :=
        rawEndpoints entries s sourceCtx sourceTy sourceRaw witness targetRaw accepted
      exact ⟨by simp [scalar,sourceView,canonical,sourceAdmitted,sourceLeast],
        by simp [scalar,targetView,canonical,targetAdmitted,targetLeast]⟩

end LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsScalarProof
