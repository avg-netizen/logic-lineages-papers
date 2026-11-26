module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem valueAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (q : Program arity) (qtag : Nat) (hq : (nodes p)[qtag]? = some ⟨arity,q⟩)
 (args : List.Vector (Term ctx) arity) (value : Term ctx)
 (he : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (call qtag args) value)) :
 Computes p G q args value := by
 intro tag ht
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag qtag arity q ht hq ctx args
 exact ⟨localTrans _ _ _ (.base hcopy) he⟩

theorem internalDispatcher : Targets.InternalDispatcher := by
 intro n p logical old x I ctx raw index fuel history
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag raw
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let rawEq := RawAddZero.equalityValue I.ctag I.atag raw
 let tail := HistoryKernel.pairCall I.ptag (.succ (.zero : Term ctx))
  (HistoryKernel.pairCall I.ptag (Term.numeral 2)
   (HistoryKernel.pairCall I.ptag (HistoryLookup.consCall I.ctag raw .zero)
    (HistoryKernel.pairCall I.ptag .zero .zero)))
 let ruleRest := HistoryKernel.pairCall I.ptag (Term.numeral 2)
  (HistoryKernel.pairCall I.ptag (HistoryLookup.consCall I.ctag raw .zero)
   (HistoryKernel.pairCall I.ptag .zero .zero))
 let expanded := HistoryKernel.pairCall I.ptag .zero (HistoryKernel.pairCall I.ptag rawEq tail)
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ expanded ::ᵥ nil
 obtain ⟨hq⟩ := RawAddZero.StatementChecks.exactInternalLine n p I.qtag I.ptag I.ctag I.atag
  I.hq I.hp I.hc I.ha ctx raw
 obtain ⟨hlog⟩ := RawAddZero.StatementChecks.exactInternalArithmetic n p old
  I.qtag I.btag I.ptag I.ctag I.atag I.vtag I.hq I.hb I.hp I.hc I.ha I.hv ctx raw
 have hlogExpanded : Hilbert.Local T ctx G
  (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.btag expanded) (.succ .zero)) :=
  localTrans _ _ _ (.base (Support.equalitySymmetry _ _
   (HistoryLookup.DestructorProof.unaryCallCongruence I.btag _ _ hq))) (.mp (.base hlog) hh)
 obtain ⟨hvb⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding n p I.ltag I.ftag I.ptag
  I.hl I.hf I.hp ctx .zero rawEq tail
 obtain ⟨hfv⟩ := ValidityProof.internalFormulaValidity n p I.vtag I.ftag I.ptag I.ctag I.atag
  I.hv I.hf I.hp I.hc I.ha ctx raw
 have hvalid : Hilbert.Local T ctx G
  (.equal (LiteralSyntaxValidator.lineCall I.ltag expanded) (.succ .zero)) :=
  localTrans _ _ _ (.base hvb) (.mp (.base hfv) hh)
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
 have harithmetic := unary p G args (RawAddZero.arithmeticLeaf old) HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G (RawAddZero.arithmeticLeaf old) I.btag I.hb (expanded ::ᵥ nil) (.succ .zero) hlogExpanded)
 let rest := HistoryDispatcher.ruleSelect 2 HistoryDispatcher.mpBranch
  (HistoryDispatcher.ruleSelect 3 HistoryDispatcher.generalizeBranch
   (HistoryDispatcher.ruleSelect 4 (.composition x HistoryDispatcher.axiomArguments) (constant 4 0)))
 have hinner : Computes p G (HistoryDispatcher.ruleSelect 1
  (applyOne (RawAddZero.arithmeticLeaf old) HistoryDispatcher.lineCode) rest) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) ht1 harithmetic
 have hrules : Computes p G (HistoryDispatcher.ruleDispatcher logical (RawAddZero.arithmeticLeaf old) x) args (.succ .zero) :=
  chooseZero p G args _ _ _ (.succ .zero) ht0 hinner
 have hvalid' := unary p G args validity HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G validity I.ltag I.hl (expanded ::ᵥ nil) (.succ .zero) hvalid)
 obtain ⟨hout⟩ := choosePositive p G args _ _ _ .zero (.succ .zero) hvalid' hrules I.dtag I.hd
 have hcg := callCongruence (T := T) (G := G) I.dtag
  (index ::ᵥ fuel ::ᵥ history ::ᵥ RawAddZero.lineCall I.qtag raw ::ᵥ nil) args (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive index))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive fuel))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive history))
       | succ i => cases i using Fin.cases with
         | zero => exact .base hq
         | succ i => exact Fin.elim0 i)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hcg hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.DispatcherProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.DispatcherProof.internalDispatcher
