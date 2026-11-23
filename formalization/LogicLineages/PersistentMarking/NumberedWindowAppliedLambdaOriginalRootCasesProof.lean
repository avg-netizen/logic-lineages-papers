module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAppliedLambdaOriginalRootCasesProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAtomicRawStep
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)
open NumberedWindowSingletonAlgorithm (output)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowRootDispatchAlgorithm (fixed parts check)
open NumberedWindowAnnotationAlgorithm (annotations)


def lambdaRaw (dom body : Nat) : Nat := packNode 2 [dom,body]

theorem lambdaView (dom body : Nat) : unpackNode (lambdaRaw dom body) = some (2,[dom,body]) :=
  nodePacked 2 [dom,body]

/-- Both actual source tags reject the unrelated original root arms.
The auxiliary case may need beta; the lambda itself cannot. -/
private theorem onlyBetaOrBottom (xs : Entries) (s : Settings) (q y sourceTag tag : Nat)
    (sourceFields ws : List Nat)
    (view : unpackNode q = some (sourceTag,sourceFields)) (shape : sourceTag = 2 ∨ sourceTag = 6) :
    parts (fixed xs s.window.2) q y tag ws =
      if tag = 6 ∧ ws = [] then NumberedWindowBinderRootAlgorithm.beta q y
      else if tag = 7 ∧ ws = [] then NumberedWindowMarkRootAlgorithm.bottom q y
      else false := by
  rcases shape with rfl | rfl
  all_goals
    have hmark (k : Nat) : NumberedWindowMarkRootAlgorithm.mark k q y = false := by
      simp [NumberedWindowMarkRootAlgorithm.mark,guarded,view,NumberedWindowMarkRootAlgorithm.markBody]
    have hlower : NumberedWindowMarkRootAlgorithm.lower q y = false := by
      simp [NumberedWindowMarkRootAlgorithm.lower,guarded,view,NumberedWindowMarkRootAlgorithm.lowerBody]
    have hselect (extra : Bool) (i : Nat) (ds : List Nat) :
        NumberedWindowSelectAlgorithm.select extra i ds q y = false := by
      simp [NumberedWindowSelectAlgorithm.select,guarded,view,NumberedWindowSelectAlgorithm.body]
    have hcopy : NumberedWindowCopyAlgorithm.copy xs s.window.2 q y = false := by
      cases hy : unpackNode y <;>
        simp [NumberedWindowCopyAlgorithm.copy,guarded,view,hy,NumberedWindowCopyAlgorithm.copyRows]
    have hstat (part : Nat) : NumberedWindowStatRootAlgorithm.stat xs s.window.2 part q y = false := by
      cases hy : unpackNode y <;>
        simp [NumberedWindowStatRootAlgorithm.stat,guarded,view,hy,NumberedWindowStatRootAlgorithm.rows]
    have hfabs : NumberedWindowBinderRootAlgorithm.fabs q y = false := by
      simp [NumberedWindowBinderRootAlgorithm.fabs,guarded,view,NumberedWindowBinderRootAlgorithm.fabsRow]
    rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
      rcases ws with _ | ⟨w,_ | ⟨u,_ | ⟨v,_ | ⟨r,rs⟩⟩⟩⟩ <;>
      simp [parts,fixed,hmark,hlower,hselect,hcopy,hstat,hfabs]

theorem dispatch (xs : Entries) (s : Settings) (q y srcTag cert : Nat)
    (srcFields : List Nat) (view : unpackNode q = some (srcTag,srcFields))
    (shape : srcTag = 2 ∨ srcTag = 6) (accepted : root xs s q cert y = true) :
    (unpackNode cert = some (6,[]) ∧ NumberedWindowBinderRootAlgorithm.beta q y = true) ∨
    (unpackNode cert = some (7,[]) ∧ NumberedWindowMarkRootAlgorithm.bottom q y = true) := by
  cases seen : unpackNode cert with
  | none => simp [root,check,seen] at accepted
  | some row =>
    rcases row with ⟨tag,fs⟩
    have tested : parts (fixed xs s.window.2) q y tag fs = true := by
      simpa only [root,check,seen,Option.any_some] using accepted
    rw [onlyBetaOrBottom xs s q y srcTag tag srcFields fs view shape] at tested
    by_cases beta : tag = 6 ∧ fs = []
    · exact Or.inl ⟨by rw [beta.1,beta.2],by simpa only [if_pos beta] using tested⟩
    · by_cases bottom : tag = 7 ∧ fs = []
      · exact Or.inr ⟨by rw [bottom.1,bottom.2],by simpa only [if_neg beta,if_pos bottom] using tested⟩
      · simp [beta,bottom] at tested

theorem bottomDestination (q y : Nat) (h : NumberedWindowMarkRootAlgorithm.bottom q y = true) :
    y = bottomRaw (annotations q).1 := by
  unfold NumberedWindowMarkRootAlgorithm.bottom guarded at h
  rw [← bottomRaw] at h
  simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,and_assoc] at h
  exact h.2.2.2.symm

theorem exact_OriginalAppliedLambdaRootCases (xs : Entries) (s : Settings)
    (dom cod body arg cert y : Nat)
    (h : root xs s (auxRaw dom cod (lambdaRaw dom body) arg) cert y = true) :
    (unpackNode cert = some (6,[]) ∧ (output arg 0 body).1 = some y) ∨
    (unpackNode cert = some (7,[]) ∧ y = bottomRaw cod) := by
  let q := auxRaw dom cod (lambdaRaw dom body) arg
  have source := auxView dom cod (lambdaRaw dom body) arg
  rcases dispatch xs s q y 6 cert [dom,cod,lambdaRaw dom body,arg] source (Or.inr rfl) h with b | b
  · have calcBeta := b.2
    simp [q,NumberedWindowBinderRootAlgorithm.beta,guarded,auxView,lambdaView,
      NumberedWindowBinderRootAlgorithm.betaRows,List.getD_eq_getElem?_getD,
      Bool.and_eq_true,and_assoc] at calcBeta
    refine Or.inl ⟨b.1,?_⟩
    have test := calcBeta.2.2
    cases result : (output arg 0 body).1 with
    | none => simp [result] at test
    | some z =>
      have hz : z = y := by simpa [result,beq_iff_eq] using test
      rw [hz]
  · have tyField : (annotations q).1 = cod := by
      simp [q,annotations,NumberedWindowAnnotationAlgorithm.termNext,auxView,
        NumberedWindowAnnotationAlgorithm.termParts,List.getD_eq_getElem?_getD]
    exact Or.inr ⟨b.1,by simpa only [tyField] using bottomDestination q y b.2⟩

theorem exact_OriginalLambdaFunctionRoot (xs : Entries) (s : Settings)
    (dom body cert y : Nat) (h : root xs s (lambdaRaw dom body) cert y = true) :
    unpackNode cert = some (7,[]) ∧ y = bottomRaw (annotations (lambdaRaw dom body)).1 := by
  rcases dispatch xs s (lambdaRaw dom body) y 2 cert [dom,body] (lambdaView dom body) (Or.inl rfl) h with b | b
  · have noBeta : NumberedWindowBinderRootAlgorithm.beta (lambdaRaw dom body) y = false := by
      cases hslot : unpackNode (0 : Nat) <;>
        simp [NumberedWindowBinderRootAlgorithm.beta,guarded,lambdaView,
          NumberedWindowBinderRootAlgorithm.betaRows,List.getD_eq_getElem?_getD,hslot]
    rw [noBeta] at b
    simp at b
  · exact ⟨b.1,bottomDestination (lambdaRaw dom body) y b.2⟩

#print axioms exact_OriginalAppliedLambdaRootCases
#print axioms exact_OriginalLambdaFunctionRoot
end LogicLineages.PersistentMarking.NumberedWindowAppliedLambdaOriginalRootCasesProof
