import LogicLineages.PersistentMarking.NativeOrientationTargets
import LogicLineages.PersistentMarking.SubstitutionProof
namespace LogicLineages.PersistentMarking.NativeFullCallProof
open Spine NativeReduction

theorem firstFullCall : NativeOrientationTargets.FirstFullCall := by
  intro τ n A B
  simp [rec2,app,apply,applyAux,consumeTypes,Head.result,P,C2,Expr.type,SubstitutionProof.emptyArgsSubstitution]

theorem secondFullCall : NativeOrientationTargets.SecondFullCall := by
  intro τ n A B
  simp [rec1,app,apply,applyAux,consumeTypes,Head.result,C2,C1,Expr.type,SubstitutionProof.emptyArgsSubstitution]

theorem thirdFullCall : NativeOrientationTargets.ThirdFullCall := by
  intro τ n A B
  simp [apply,applyAux,consumeTypes,C1,C0,Head.result,stepType,Expr.type,SubstitutionProof.emptyArgsSubstitution]
end LogicLineages.PersistentMarking.NativeFullCallProof
