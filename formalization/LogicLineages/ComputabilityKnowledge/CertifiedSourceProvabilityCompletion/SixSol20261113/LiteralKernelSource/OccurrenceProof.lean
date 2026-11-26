module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.OccurrenceProof
open GorbowPRProgram GorbowPRRegistry HistoryRuleSuffix

private theorem chooseTest {n : Nat} {a : Packed} {test yes no : Program n} (h : Occurs a test) :
    Occurs a (choose test yes no) := .compositionArgument HistoryCodec.select _ 0 h
private theorem chooseZero {n : Nat} {a : Packed} {test yes no : Program n} (h : Occurs a yes) :
    Occurs a (choose test yes no) := .compositionArgument HistoryCodec.select _ 1 h
private theorem choosePositive {n : Nat} {a : Packed} {test yes no : Program n} (h : Occurs a no) :
    Occurs a (choose test yes no) := .compositionArgument HistoryCodec.select _ 2 h
private theorem binaryFirst {n : Nat} {a : Packed} {f : Program 2} {x y : Program n} (h : Occurs a x) :
    Occurs a (applyTwo f x y) := .compositionArgument f _ 0 h
private theorem binarySecond {n : Nat} {a : Packed} {f : Program 2} {x y : Program n} (h : Occurs a y) :
    Occurs a (applyTwo f x y) := .compositionArgument f _ 1 h
private theorem conjunctionRight {n : Nat} {a : Packed} {x y : Program n} (h : Occurs a y) :
    Occurs a (conjunction x y) := choosePositive h

theorem mpBodyAppend : Occurs ⟨2,HistoryAppend.append⟩ mpBody := by
  have happ : Occurs ⟨2,HistoryAppend.append⟩
      (applyTwo HistoryAppend.append (entryPart true (.projection (3 : Fin 4))) (.projection 1)) :=
    .compositionFunction HistoryAppend.append _ (.here _ rfl)
  have himp : Occurs ⟨2,HistoryAppend.append⟩
      (applyTwo HistoryCodec.cons (constant 4 7)
        (applyTwo HistoryAppend.append (entryPart true (.projection (3 : Fin 4))) (.projection 1))) := binarySecond happ
  have heq : Occurs ⟨2,HistoryAppend.append⟩
      (applyTwo equalCode (entryPart true (.projection (2 : Fin 4)))
        (applyTwo HistoryCodec.cons (constant 4 7)
          (applyTwo HistoryAppend.append (entryPart true (.projection (3 : Fin 4))) (.projection 1)))) := binarySecond himp
  have hg : Occurs ⟨2,HistoryAppend.append⟩ HistoryRuleSuffix.GuardProof.mpGuard :=
    conjunctionRight (conjunctionRight heq)
  have hs : Occurs ⟨2,HistoryAppend.append⟩ HistoryRuleSuffix.GuardProof.mpSecond := choosePositive hg
  exact choosePositive hs

theorem mpCheckAppend : Occurs ⟨2,HistoryAppend.append⟩ mpCheck :=
  .compositionFunction mpBody mpArguments mpBodyAppend

theorem dispatcherAppend (v l a : Program 1) (x : Program 3) :
    Occurs ⟨2,HistoryAppend.append⟩ (HistoryDispatcher.lineDispatcher v l a x) := by
  have hm : Occurs ⟨2,HistoryAppend.append⟩ HistoryDispatcher.mpBranch :=
    conjunctionRight (.compositionFunction mpCheck HistoryDispatcher.mpArguments mpCheckAppend)
  have h2 : Occurs ⟨2,HistoryAppend.append⟩
      (HistoryDispatcher.ruleSelect 2 HistoryDispatcher.mpBranch
        (HistoryDispatcher.ruleSelect 3 HistoryDispatcher.generalizeBranch
          (HistoryDispatcher.ruleSelect 4 (.composition x HistoryDispatcher.axiomArguments) (constant 4 0)))) :=
    choosePositive hm
  have h1 : Occurs ⟨2,HistoryAppend.append⟩
      (HistoryDispatcher.ruleSelect 1 (applyOne a HistoryDispatcher.lineCode)
        (HistoryDispatcher.ruleSelect 2 HistoryDispatcher.mpBranch
          (HistoryDispatcher.ruleSelect 3 HistoryDispatcher.generalizeBranch
            (HistoryDispatcher.ruleSelect 4 (.composition x HistoryDispatcher.axiomArguments) (constant 4 0))))) :=
    chooseZero h2
  have h0 : Occurs ⟨2,HistoryAppend.append⟩ (HistoryDispatcher.ruleDispatcher l a x) := chooseZero h1
  exact conjunctionRight h0

theorem kernelAppend (v l a : Program 1) (x : Program 3) :
    Occurs ⟨2,HistoryAppend.append⟩ (HistoryKernel.kernel v l a x) := by
  have hd : Occurs ⟨2,HistoryAppend.append⟩ (HistoryKernel.checkedLine v l a x) :=
    .compositionFunction (HistoryDispatcher.lineDispatcher v l a x) HistoryKernel.dispatcherArguments (dispatcherAppend v l a x)
  have ht : Occurs ⟨2,HistoryAppend.append⟩ (HistoryKernel.acceptedTest v l a x) := binaryFirst hd
  have ha : Occurs ⟨2,HistoryAppend.append⟩ (HistoryKernel.acceptedOption v l a x) := chooseTest ht
  have ho : Occurs ⟨2,HistoryAppend.append⟩ (HistoryKernel.nextOption v l a x) := choosePositive ha
  have hn : Occurs ⟨2,HistoryAppend.append⟩ (HistoryKernel.nextState v l a x) := binaryFirst ho
  exact choosePositive hn

theorem appendOffset (v l a : Program 1) (x : Program 3) :
    ∃ offset : Nat, (nodes (HistoryKernel.kernel v l a x))[offset]? = some (⟨2,HistoryAppend.append⟩ : Packed) := by
  obtain ⟨offset,hm,he⟩ := (GorbowPRRegistry.Proof.taggedCoverage 3 (HistoryKernel.kernel v l a x)
    ⟨2,HistoryAppend.append⟩).mp (kernelAppend v l a x)
  exact ⟨offset,he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.OccurrenceProof
