module
public import LogicLineages.PersistentMarking.NumberedWindowAppliedLambdaOriginalRootCasesProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionContextProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionWrappedProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAppliedLambdaOriginalRunCasesProof
open NumberedWindowAppliedLambdaOriginalRootCasesProof
  (lambdaRaw lambdaView exact_OriginalAppliedLambdaRootCases exact_OriginalLambdaFunctionRoot)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicRawStep (bottomRaw)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowAtomicApplicationReductionContextProof (auxContext)
open NumberedWindowAtomicApplicationReductionWrappedProof (terminal)
open NumberedWindowRawContextAlgorithm (RawRoot Frame next context run tick iterate raw windowStep)
open NumberedWindowConcreteCheckers (root step)
open NumberedWindowSingletonAlgorithm (output)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAnnotationAlgorithm (annotations)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings admitted)

/-- On the exact original positive raw run, retain either the original
root wrapper or the exact proper frame and remaining original fuel. -/
private theorem splitRun (R : RawRoot) (q w y fuel : Nat)
    (h : run R fuel q w y = true) :
    (∃ cert, unpackNode w = some (0,[cert]) ∧ R q cert y = true) ∨
    (∃ tag fs child childW childY n,
      unpackNode w = some (tag,fs) ∧ next tag fs q y = some (child,childW,childY) ∧
      run R n child childW childY = true) := by
  cases fuel with
  | zero => simp [run,iterate] at h
  | succ fuel =>
    cases seen : unpackNode w with
    | none => simp [run,iterate,tick,seen,terminal] at h
    | some row =>
      rcases row with ⟨tag,fs⟩
      by_cases isRoot : tag = 0 ∧ ∃ cert, fs = [cert]
      · obtain ⟨rfl,cert,rfl⟩ := isRoot
        exact Or.inl ⟨cert,by first | exact seen | rfl,
          by simpa only [run,iterate,tick,seen,terminal] using h⟩
      · have first : tick R (false,some (q,w,y)) = (false,next tag fs q y) := by
          rcases tag with _ | tag
          · rcases fs with _ | ⟨cert,_ | ⟨x,rest⟩⟩
            · simp [tick,seen]
            · exact False.elim (isRoot ⟨rfl,cert,rfl⟩)
            · simp [tick,seen]
          · simp [tick,seen]
        have rests := h
        simp only [run,iterate,first] at rests
        cases chosen : next tag fs q y with
        | none => simp [chosen,terminal] at rests
        | some frame =>
          rcases frame with ⟨cq,cw,cy⟩
          exact Or.inr ⟨tag,fs,cq,cw,cy,fuel,by first | exact seen | rfl,chosen,
            by simpa only [run,chosen] using rests⟩

private theorem lambdaContext (tag : Nat) (fs : List Nat) (dom body y : Nat) (F : Frame)
    (h : next tag fs (lambdaRaw dom body) y = some F) :
    ∃ child out, tag = 1 ∧ fs = [child] ∧ y = lambdaRaw dom out ∧ F = (body,child,out) := by
  cases hy : unpackNode y with
  | none => simp [next,lambdaView,hy] at h
  | some row =>
    rcases row with ⟨dest,slots⟩
    rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
      rcases fs with _ | ⟨w,_ | ⟨a,as⟩⟩ <;>
      simp [next,lambdaView,hy,context] at h
    rcases dest with _ | _ | _ | i <;>
      rcases slots with _ | ⟨dom',_ | ⟨out,_ | ⟨x,xs⟩⟩⟩ <;>
      simp [context] at h
    have same : dom = dom' ∧ (body,w,out) = F := by simpa [beq_iff_eq] using h
    obtain ⟨eq,frame⟩ := same
    subst dom'
    exact ⟨w,out,rfl,rfl,(codeOfNode hy).trans (codeOfNode (lambdaView dom out)).symm,frame.symm⟩

/-- The complete actual raw applied-lambda classification. Proper
function context either bottoms the inner lambda at its real raw
annotation, or goes under exactly that lambda binder. -/
def AppliedLambdaRawCases (R : RawRoot) (dom cod body arg witness y : Nat) : Prop :=
  (∃ cert, unpackNode witness = some (0,[cert]) ∧ unpackNode cert = some (6,[]) ∧
    (output arg 0 body).1 = some y) ∨
  (∃ cert, unpackNode witness = some (0,[cert]) ∧ unpackNode cert = some (7,[]) ∧ y = bottomRaw cod) ∨
  (∃ child cert, unpackNode witness = some (5,[child]) ∧
    unpackNode child = some (0,[cert]) ∧ unpackNode cert = some (7,[]) ∧
    y = auxRaw dom cod (bottomRaw (annotations (lambdaRaw dom body)).1) arg) ∨
  (∃ child bodyCert bodyOut fuel, unpackNode witness = some (5,[child]) ∧
    unpackNode child = some (1,[bodyCert]) ∧
    y = auxRaw dom cod (lambdaRaw dom bodyOut) arg ∧
    run R fuel body bodyCert bodyOut = true)

theorem exact_OriginalAppliedLambdaRunCases (xs : Entries) (s : Settings)
    (dom cod body arg witness y fuel : Nat)
    (h : run (root xs s) fuel (auxRaw dom cod (lambdaRaw dom body) arg) witness y = true) :
    AppliedLambdaRawCases (root xs s) dom cod body arg witness y := by
  rcases splitRun (root xs s) (auxRaw dom cod (lambdaRaw dom body) arg) witness y fuel h with
    ⟨cert,wrap,ok⟩ | ⟨tag,fs,cq,cw,cy,n,wrap,advance,ok⟩
  · rcases exact_OriginalAppliedLambdaRootCases xs s dom cod body arg cert y ok with beta | bottom
    · exact Or.inl ⟨cert,wrap,beta.1,beta.2⟩
    · exact Or.inr (Or.inl ⟨cert,wrap,bottom.1,bottom.2⟩)
  · obtain ⟨child,out,tagEq,fields,yEq,triple⟩ :=
      auxContext tag fs dom cod (lambdaRaw dom body) arg y (cq,cw,cy) advance
    have outer : unpackNode witness = some (5,[child]) := by rw [wrap,tagEq,fields]
    have lp : run (root xs s) n (lambdaRaw dom body) child out = true := by
      have eq := congrArg (fun t : Frame => run (root xs s) n t.1 t.2.1 t.2.2) triple
      exact eq ▸ ok
    rcases splitRun (root xs s) (lambdaRaw dom body) child out n lp with
      ⟨cert,cwrap,last⟩ | ⟨tag',fs',bq,bw,by',left,cwrap,forward,last⟩
    · obtain ⟨certTag,result⟩ := exact_OriginalLambdaFunctionRoot xs s dom body cert out last
      exact Or.inr (Or.inr (Or.inl ⟨child,cert,outer,cwrap,certTag,yEq.trans (by rw [result])⟩))
    · obtain ⟨bodyCert,bodyOut,tagEq',fields',outEq,triple'⟩ :=
        lambdaContext tag' fs' dom body out (bq,bw,by') forward
      have inner : unpackNode child = some (1,[bodyCert]) := by rw [cwrap,tagEq',fields']
      have actual : run (root xs s) left body bodyCert bodyOut = true := by
        have eq := congrArg (fun t : Frame => run (root xs s) left t.1 t.2.1 t.2.2) triple'
        exact eq ▸ last
      exact Or.inr (Or.inr (Or.inr ⟨child,bodyCert,bodyOut,left,outer,inner,
        yEq.trans (by rw [outEq]),actual⟩))

theorem exact_OriginalAppliedLambdaStepCases (xs : Entries) (s : Settings) (ctx : List Nat)
    (ty dom cod body arg witness y : Nat)
    (h : step xs s ctx ty (auxRaw dom cod (lambdaRaw dom body) arg) witness y = true) :
    admitted s ctx ty y = true ∧ AppliedLambdaRawCases (root xs s) dom cod body arg witness y := by
  simp only [step,windowStep,raw,Bool.and_eq_true,and_assoc] at h
  exact ⟨h.2.2.2.2,exact_OriginalAppliedLambdaRunCases xs s dom cod body arg witness y witness h.2.2.1⟩

#print axioms exact_OriginalAppliedLambdaRunCases
#print axioms exact_OriginalAppliedLambdaStepCases
end LogicLineages.PersistentMarking.NumberedWindowAppliedLambdaOriginalRunCasesProof
