module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingFreshProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingScopeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingOperationsProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingFAbsProof
open NumberedWindowSyntax NumberedWindowClosing NumberedWindowFrameTargets
open NumberedWindowClosingFreshProof (realizedArgs unchangedArgs)
open NumberedWindowClosingScopeProof (belowEmpty shiftBases shiftExtras)
open NameBridge (freeOccurs)

theorem ownerBody : ClosingRecoversFAbsBody := by
  intro f σ τ x bs es n k Bs Es ht hf hb he
  have hFresh := Bool.or_eq_false_iff.mp hf
  have hBsFresh := unchangedArgs (σ,x) 0 Bs (realizedArgs (σ,x) hb hFresh.1)
  have hEsFresh := unchangedArgs (σ,x) 0 Es (realizedArgs (σ,x) he hFresh.2)
  have hFree : closeAt (σ,x) 0 (.free σ x) = .bound σ 0 := by simp [closeAt]
  cases ht with
  | marked hbase hextra =>
    have hb' := (NumberedWindowRealizationTypingProof.typedArgs hb).1 _ _ hbase
    have he' := (NumberedWindowRealizationTypingProof.typedArgs he).2 _ hextra
    change NTerm.numbered f τ k (closeArgsAt (σ,x) 0 Bs)
      (closeArgsAt (σ,x) 0 (Es.append (.cons (.free σ x) .nil))) = _
    simp only [NumberedWindowClosingOperationsProof.append,hBsFresh,hEsFresh,
      closeArgsAt,hFree,openNumbered,shiftBases _ _ _ 1 0 hb' belowEmpty,
      shiftExtras _ _ 1 0 he' belowEmpty]

end LogicLineages.PersistentMarking.NumberedWindowClosingFAbsProof
