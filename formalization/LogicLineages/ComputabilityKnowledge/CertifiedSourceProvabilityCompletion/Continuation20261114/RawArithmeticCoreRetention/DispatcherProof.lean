module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.LeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem dispatcher {n ctx : Nat} (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x) (formula payload ann index fuel : Term ctx) (history : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero))
   (.imp (.equal (leafCall I.oldTag (line I.ptag formula payload ann)) (.succ .zero))
    (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history (line I.ptag formula payload ann)) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero)
 let K := Formula.equal (leafCall I.oldTag (line I.ptag formula payload ann)) (.succ .zero)
 let G := [K,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hkValid : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 let rawEq := formula
 let ruleRest := HistoryKernel.pairCall I.ptag payload
  (HistoryKernel.pairCall I.ptag ann (HistoryKernel.pairCall I.ptag .zero .zero))
 let tail := HistoryKernel.pairCall I.ptag (.succ (.zero : Term ctx)) ruleRest
 let expanded := line I.ptag formula payload ann
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ expanded ::ᵥ nil
 obtain ⟨hr⟩ := LeafProof.internalLeafRetention n p old I.oldTag I.newTag I.ho I.hn ctx expanded
 have hlogExpanded : Hilbert.Local T ctx G
  (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.newTag expanded) (.succ .zero)) := .mp (.base hr) hkValid
 obtain ⟨hvb⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding n p I.ltag I.ftag I.ptag
  I.hl I.hf I.hp ctx .zero rawEq tail
 have hvalid : Hilbert.Local T ctx G
  (.equal (LiteralSyntaxValidator.lineCall I.ltag expanded) (.succ .zero)) := localTrans _ _ _ (.base hvb) hh
 have hline : Computes p G HistoryDispatcher.lineCode args expanded := projection p G args 3
 have hr1 := RawReflexivity.LogicalProof.decoded p G I.ptag I.hp args HistoryDispatcher.lineCode true
  .zero (HistoryKernel.pairCall I.ptag rawEq tail) hline
 have hr2 := RawReflexivity.LogicalProof.decoded p G I.ptag I.hp args
  (HistoryDispatcher.right HistoryDispatcher.lineCode) true rawEq tail hr1
 have hrule : Computes p G HistoryDispatcher.ruleCode args (.succ .zero) :=
  RawReflexivity.LogicalProof.decoded p G I.ptag I.hp args
   (HistoryDispatcher.right (HistoryDispatcher.right HistoryDispatcher.lineCode)) false (.succ .zero) ruleRest hr2
 have ht0 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 0)
  (.succ .zero) .zero .zero hrule (constantValue p G args 0)
  (equalFalse p G (.succ .zero) .zero (.arithmetic (.succNotZero .zero)))
 have ht1 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 1)
  (.succ .zero) (.succ .zero) (.succ .zero) hrule (constantValue p G args 1)
  (equalDiagonal p G (.succ .zero))
 have harithmetic := unary p G args (RawMultiplication.arithmeticLeaf old) HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (RawRightReplaceDispatcher.DispatcherProof.valueAt p G (RawMultiplication.arithmeticLeaf old) I.newTag I.hn (expanded ::ᵥ nil) (.succ .zero) hlogExpanded)
 let rest := HistoryDispatcher.ruleSelect 2 HistoryDispatcher.mpBranch
  (HistoryDispatcher.ruleSelect 3 HistoryDispatcher.generalizeBranch
   (HistoryDispatcher.ruleSelect 4 (.composition x HistoryDispatcher.axiomArguments) (constant 4 0)))
 have hinner : Computes p G (HistoryDispatcher.ruleSelect 1
  (applyOne (RawMultiplication.arithmeticLeaf old) HistoryDispatcher.lineCode) rest) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) ht1 harithmetic
 have hrules : Computes p G (HistoryDispatcher.ruleDispatcher logical (RawMultiplication.arithmeticLeaf old) x) args (.succ .zero) :=
  chooseZero p G args _ _ _ (.succ .zero) ht0 hinner
 have hvalid' := unary p G args validity HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (RawRightReplaceDispatcher.DispatcherProof.valueAt p G validity I.ltag I.hl (expanded ::ᵥ nil) (.succ .zero) hvalid)
 obtain ⟨hout⟩ := choosePositive p G args _ _ _ .zero (.succ .zero) hvalid' hrules I.dtag I.hd
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.DispatcherProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.DispatcherProof.dispatcher
