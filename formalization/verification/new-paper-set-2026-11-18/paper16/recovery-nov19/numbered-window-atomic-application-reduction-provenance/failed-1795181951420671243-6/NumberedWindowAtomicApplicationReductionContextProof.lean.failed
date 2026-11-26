module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionContextProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm (next context)

theorem auxContext : ExactAuxProperFunctionContext := by
  intro tag ws dom cod fn arg y out found
  cases hy : unpackNode y with
  | none => simp [next,auxView,hy] at found
  | some dest =>
    rcases dest with ⟨destTag,destFields⟩
    rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
      rcases ws with _ | ⟨w,_ | ⟨p,ps⟩⟩ <;>
      simp [next,auxView,hy,context] at found
    rcases destTag with _ | _ | _ | _ | _ | _ | _ | i <;>
      rcases destFields with _ | ⟨dom',_ | ⟨cod',_ | ⟨g,_ | ⟨arg',_ | ⟨p,ps⟩⟩⟩⟩⟩ <;>
      simp [context] at found
    have he : dom = dom' ∧ cod = cod' ∧ arg = arg' ∧ (fn,w,g) = out := by
      simpa [Bool.and_eq_true,beq_iff_eq,and_assoc] using found
    obtain ⟨sameDom,sameCod,sameArg,sameFrame⟩ := he
    subst dom'
    subst cod'
    subst arg'
    exact ⟨w,g,rfl,rfl,codeOfNode hy,sameFrame.symm⟩

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionContextProof
