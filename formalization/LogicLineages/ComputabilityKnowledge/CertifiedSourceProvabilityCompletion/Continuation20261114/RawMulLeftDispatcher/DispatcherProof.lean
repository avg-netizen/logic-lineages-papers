module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftDispatcher.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftDispatcher.DispatcherProof
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
 intro n p old arithmetic x I ctx raw rawB rawV index fuel history
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.validatorTag raw
 let K := RawReflexivityDispatcher.valid I.validatorTag rawB
 let L := RawReflexivityDispatcher.valid I.validatorTag rawV
 let G := [L,K,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hk : Hilbert.Local T ctx G K := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hlv : Hilbert.Local T ctx G L := .hypothesis List.mem_cons_self
 let rawEq := RawMulLeftReplace.formulaValue I.consTag I.appendTag raw rawB rawV
 let args3 := HistoryLookup.consCall I.consTag (RawMulLeftReplace.templateValue I.consTag I.appendTag raw rawV)
  (HistoryLookup.consCall I.consTag raw (HistoryLookup.consCall I.consTag rawB .zero))
 let ruleRest := HistoryKernel.pairCall I.pairTag (Term.numeral 12)
  (HistoryKernel.pairCall I.pairTag args3 (HistoryKernel.pairCall I.pairTag .zero .zero))
 let tail := HistoryKernel.pairCall I.pairTag (.zero : Term ctx) ruleRest
 let expanded := HistoryKernel.pairCall I.pairTag .zero (HistoryKernel.pairCall I.pairTag rawEq tail)
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ expanded ::ᵥ nil
 obtain ⟨hq⟩ := RawMulLeftReplace.StatementChecks.exactInternalLine n p I.qtag I.pairTag I.consTag I.appendTag
  I.hq I.hp I.hc I.ha ctx raw rawB rawV
 obtain ⟨hlog⟩ := RawMulLeftAcceptance.StatementChecks.exactLogical n p old I.toAcceptance ctx raw rawB rawV
 have hlogExpanded : Hilbert.Local T ctx G
  (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.logicalTag expanded) (.succ .zero)) :=
  localTrans _ _ _ (.base (Support.equalitySymmetry _ _
   (HistoryLookup.DestructorProof.unaryCallCongruence I.logicalTag _ _ hq))) (.mp (.mp (.mp (.base hlog) hh) hk) hlv)
 obtain ⟨hvb⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding n p I.ltag I.ftag I.pairTag
  I.hlineValidator I.hf I.hp ctx .zero rawEq tail
 obtain ⟨hfv⟩ := ValidityProof.internalFormulaValidity n p I.validatorTag I.ftag I.pairTag I.consTag I.appendTag
  I.hv I.hf I.hp I.hc I.ha ctx raw rawB rawV
 have hvalid : Hilbert.Local T ctx G
  (.equal (LiteralSyntaxValidator.lineCall I.ltag expanded) (.succ .zero)) :=
  localTrans _ _ _ (.base hvb) (.mp (.mp (.mp (.base hfv) hh) hk) hlv)
 have hline : Computes p G HistoryDispatcher.lineCode args expanded := projection p G args 3
 have hr1 := RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args HistoryDispatcher.lineCode true
  .zero (HistoryKernel.pairCall I.pairTag rawEq tail) hline
 have hr2 := RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args
  (HistoryDispatcher.right HistoryDispatcher.lineCode) true rawEq tail hr1
 have hrule : Computes p G HistoryDispatcher.ruleCode args .zero :=
  RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args
   (HistoryDispatcher.right (HistoryDispatcher.right HistoryDispatcher.lineCode)) false .zero ruleRest hr2
 have ht0 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 0) .zero .zero (.succ .zero)
  hrule (constantValue p G args 0) (equalDiagonal p G .zero)
 have hlogical := unary p G args (RawMulLeftReplace.logicalLeaf old) HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G (RawMulLeftReplace.logicalLeaf old) I.logicalTag I.hlogical (expanded ::ᵥ nil) (.succ .zero) hlogExpanded)
 have hrules : Computes p G (HistoryDispatcher.ruleDispatcher (RawMulLeftReplace.logicalLeaf old) arithmetic x) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) ht0 hlogical
 have hvalid' := unary p G args validity HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G validity I.ltag I.hlineValidator (expanded ::ᵥ nil) (.succ .zero) hvalid)
 obtain ⟨hout⟩ := choosePositive p G args _ _ _ .zero (.succ .zero) hvalid' hrules I.dtag I.hdispatcher
 have hcg := callCongruence (T := T) (G := G) I.dtag
  (index ::ᵥ fuel ::ᵥ history ::ᵥ RawMulLeftReplace.lineCall I.qtag raw rawB rawV ::ᵥ nil) args (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive index))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive fuel))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive history))
       | succ i => cases i using Fin.cases with
         | zero => exact .base hq
         | succ i => exact Fin.elim0 i)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcg hout))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftDispatcher.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftDispatcher.DispatcherProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftDispatcher.DispatcherProof.internalDispatcher
