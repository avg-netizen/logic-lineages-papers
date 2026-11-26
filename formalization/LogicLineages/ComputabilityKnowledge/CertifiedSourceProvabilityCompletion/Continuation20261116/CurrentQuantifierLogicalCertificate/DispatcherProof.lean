module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.MachineInterface
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.DispatcherProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open RawEqualityInstantiationDispatcher.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
/-- Literal line binding, tuple rule selection, and original dispatcher branches.
No native calibration, successful run, or positive fuel is used. -/
theorem internalDispatcher {n ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3)
 (isS : Bool) (I : Installation p f lhs rhs rawOld arithmetic x isS) (formula leftTerm index fuel history : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm)
   (.equal (GorbowPRDefiningEquations.call I.dispatcherTag
    (index ::ᵥ fuel ::ᵥ history ::ᵥ OriginalQuantifierLogicalProducers.lineCall I.quantifierTag formula leftTerm ::ᵥ nil)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let rawEq := OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm
 let args3 := OriginalQuantifierLogicalProducers.argumentsValue isS I.ctag formula leftTerm
 let ruleRest := HistoryKernel.pairCall I.ptag (Term.numeral (if isS then 10 else 2))
  (HistoryKernel.pairCall I.ptag args3 (HistoryKernel.pairCall I.ptag .zero .zero))
 let tail := HistoryKernel.pairCall I.ptag (.zero : Term ctx) ruleRest
 let expanded := HistoryKernel.pairCall I.ptag .zero (HistoryKernel.pairCall I.ptag rawEq tail)
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ expanded ::ᵥ nil
 have hlineComputed := OriginalQuantifierLogicalProducers.LineGraph.lineAt p G I.ptag I.ctag I.atag
  I.h_ptag I.h_ctag I.h_atag isS (.projection 0) (.projection 1)
  (formula ::ᵥ leftTerm ::ᵥ nil) formula leftTerm
  (projection p G _ 0) (projection p G _ 1)
 obtain ⟨hq⟩ := hlineComputed I.quantifierTag I.h_quantifierTag
 have hinner := WrapperProof.inner p G rawOld isS I.ptag I.ctag I.atag I.fval
  I.h_ptag I.h_ctag I.h_atag I.h_fval formula leftTerm hh
 have hcum := WrapperProof.cumulative p G f lhs rhs _ (expanded ::ᵥ nil) hinner
 obtain ⟨hlogExpanded⟩ := hcum I.logicalTag I.h_logicalTag
 obtain ⟨hvb⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding n p I.lineTag I.fval I.ptag
  I.h_lineTag I.h_fval I.h_ptag ctx .zero rawEq tail
 obtain ⟨hfv⟩ := ValidityProof.conclusionValidity p (baseLogical f lhs rhs rawOld) arithmetic x I.toInstallation isS formula leftTerm
 have hvalid : Hilbert.Local T ctx G
  (.equal (LiteralSyntaxValidator.lineCall I.lineTag expanded) (.succ .zero)) :=
  localTrans _ _ _ (.base hvb) (.mp (.base hfv) hh)
 have hline : Computes p G HistoryDispatcher.lineCode args expanded := projection p G args 3
 have hr1 := RawReflexivity.LogicalProof.decoded p G I.ptag I.h_ptag args HistoryDispatcher.lineCode true
  .zero (HistoryKernel.pairCall I.ptag rawEq tail) hline
 have hr2 := RawReflexivity.LogicalProof.decoded p G I.ptag I.h_ptag args
  (HistoryDispatcher.right HistoryDispatcher.lineCode) true rawEq tail hr1
 have hrule : Computes p G HistoryDispatcher.ruleCode args .zero :=
  RawReflexivity.LogicalProof.decoded p G I.ptag I.h_ptag args
   (HistoryDispatcher.right (HistoryDispatcher.right HistoryDispatcher.lineCode)) false .zero ruleRest hr2
 have ht0 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 0) .zero .zero (.succ .zero)
  hrule (constantValue p G args 0) (equalDiagonal p G .zero)
 have hlogical := unary p G args (logical f lhs rhs rawOld) HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G (logical f lhs rhs rawOld) I.logicalTag I.h_logicalTag (expanded ::ᵥ nil) (.succ .zero) hlogExpanded)
 have hrules : Computes p G (HistoryDispatcher.ruleDispatcher (logical f lhs rhs rawOld) arithmetic x) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) ht0 hlogical
 have hvalid' := unary p G args validity HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G validity I.lineTag I.h_lineTag (expanded ::ᵥ nil) (.succ .zero) hvalid)
 obtain ⟨hout⟩ := choosePositive p G args _ _ _ .zero (.succ .zero) hvalid' hrules I.dispatcherTag I.h_dispatcherTag
 have hcg := callCongruence (T := T) (G := G) I.dispatcherTag
  (index ::ᵥ fuel ::ᵥ history ::ᵥ OriginalQuantifierLogicalProducers.lineCall I.quantifierTag formula leftTerm ::ᵥ nil) args (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive index))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive fuel))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive history))
       | succ i => cases i using Fin.cases with
         | zero => exact hq
         | succ i => exact Fin.elim0 i)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hcg hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.DispatcherProof
