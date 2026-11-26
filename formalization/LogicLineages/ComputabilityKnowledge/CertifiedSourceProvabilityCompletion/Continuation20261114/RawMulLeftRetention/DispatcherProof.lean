module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftRetention.LeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftRetention.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem dispatcher {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x) (formula payload ann index fuel : Term ctx) (history : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero))
   (.imp (.equal (RawLogicalRetention.leafCall I.oldTag (line I.ptag formula payload ann)) (.succ .zero))
    (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history (line I.ptag formula payload ann)) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero)
 let K := Formula.equal (RawLogicalRetention.leafCall I.oldTag (line I.ptag formula payload ann)) (.succ .zero)
 let G := [K,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hkValid : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 let rawEq := formula
 let ruleRest := HistoryKernel.pairCall I.ptag payload
  (HistoryKernel.pairCall I.ptag ann (HistoryKernel.pairCall I.ptag .zero .zero))
 let tail := HistoryKernel.pairCall I.ptag (.zero : Term ctx) ruleRest
 let expanded := line I.ptag formula payload ann
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ expanded ::ᵥ nil
 obtain ⟨hr⟩ := LeafProof.internalRetention n p old I.oldTag I.newTag I.ho I.hn ctx expanded
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
 have hrule : Computes p G HistoryDispatcher.ruleCode args .zero :=
  RawReflexivity.LogicalProof.decoded p G I.ptag I.hp args
   (HistoryDispatcher.right (HistoryDispatcher.right HistoryDispatcher.lineCode)) false .zero ruleRest hr2
 have ht0 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 0) .zero .zero (.succ .zero)
  hrule (constantValue p G args 0) (equalDiagonal p G .zero)
 have hlogical := unary p G args (RawMulLeftReplace.logicalLeaf old) HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (RawMulLeftDispatcher.DispatcherProof.valueAt p G (RawMulLeftReplace.logicalLeaf old) I.newTag I.hn (expanded ::ᵥ nil) (.succ .zero) hlogExpanded)
 have hrules : Computes p G (HistoryDispatcher.ruleDispatcher (RawMulLeftReplace.logicalLeaf old) arithmetic x) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) ht0 hlogical
 have hvalid' := unary p G args validity HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (RawMulLeftDispatcher.DispatcherProof.valueAt p G validity I.ltag I.hl (expanded ::ᵥ nil) (.succ .zero) hvalid)
 obtain ⟨hout⟩ := choosePositive p G args _ _ _ .zero (.succ .zero) hvalid' hrules I.dtag I.hd
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftRetention.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftRetention.DispatcherProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftRetention.DispatcherProof.dispatcher
