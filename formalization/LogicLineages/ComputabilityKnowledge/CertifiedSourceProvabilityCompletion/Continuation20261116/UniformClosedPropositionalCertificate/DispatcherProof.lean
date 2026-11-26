module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.DispatcherProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open RawEqualityInstantiationDispatcher.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
/-- Literal line binding, tuple rule selection, and original dispatcher branches.
No native calibration, successful run, or positive fuel is used. -/
theorem internalDispatcher {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (isS : Bool) (I : Installation p old arithmetic x isS) (formula leftTerm rightTerm index fuel history : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedPropositional.guards isS I.fval formula leftTerm rightTerm)
   (.equal (GorbowPRDefiningEquations.call I.dispatcherTag
    (index ::ᵥ fuel ::ᵥ history ::ᵥ UniformClosedPropositional.lineCall I.constructorTag formula leftTerm rightTerm ::ᵥ nil)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := UniformClosedPropositional.guards isS I.fval formula leftTerm rightTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let rawEq := UniformClosedPropositional.conclusionValue isS I.ctag I.atag formula leftTerm rightTerm
 let args3 := UniformClosedPropositional.argumentsValue isS I.ctag formula leftTerm rightTerm
 let ruleRest := HistoryKernel.pairCall I.ptag (Term.numeral (if isS then 1 else 0))
  (HistoryKernel.pairCall I.ptag args3 (HistoryKernel.pairCall I.ptag .zero .zero))
 let tail := HistoryKernel.pairCall I.ptag (.zero : Term ctx) ruleRest
 let expanded := HistoryKernel.pairCall I.ptag .zero (HistoryKernel.pairCall I.ptag rawEq tail)
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ expanded ::ᵥ nil
 obtain ⟨hq⟩ := UniformClosedPropositional.StatementChecks.exactInternalLine n p isS I.constructorTag I.ptag I.ctag I.atag
  I.h_constructorTag I.h_ptag I.h_ctag I.h_atag ctx formula leftTerm rightTerm
 obtain ⟨hlog⟩ := UniformClosedPropositional.StatementChecks.exactInternalLogical n p old isS
  I.constructorTag I.logicalTag I.ptag I.ctag I.atag I.fval
  I.h_constructorTag I.h_logicalTag I.h_ptag I.h_ctag I.h_atag I.h_fval ctx formula leftTerm rightTerm
 have hlogExpanded : Hilbert.Local T ctx G
  (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.logicalTag expanded) (.succ .zero)) :=
  localTrans _ _ _ (.base (Support.equalitySymmetry _ _
   (HistoryLookup.DestructorProof.unaryCallCongruence I.logicalTag _ _ hq))) (.mp (.base hlog) hh)
 obtain ⟨hvb⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding n p I.lineTag I.fval I.ptag
  I.h_lineTag I.h_fval I.h_ptag ctx .zero rawEq tail
 obtain ⟨hfv⟩ := ValidityProof.conclusionValidity p old arithmetic x isS I formula leftTerm rightTerm
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
 have hlogical := unary p G args (UniformClosedPropositional.logicalLeaf old) HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G (UniformClosedPropositional.logicalLeaf old) I.logicalTag I.h_logicalTag (expanded ::ᵥ nil) (.succ .zero) hlogExpanded)
 have hrules : Computes p G (HistoryDispatcher.ruleDispatcher (UniformClosedPropositional.logicalLeaf old) arithmetic x) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) ht0 hlogical
 have hvalid' := unary p G args validity HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p G validity I.lineTag I.h_lineTag (expanded ::ᵥ nil) (.succ .zero) hvalid)
 obtain ⟨hout⟩ := choosePositive p G args _ _ _ .zero (.succ .zero) hvalid' hrules I.dispatcherTag I.h_dispatcherTag
 have hcg := callCongruence (T := T) (G := G) I.dispatcherTag
  (index ::ᵥ fuel ::ᵥ history ::ᵥ UniformClosedPropositional.lineCall I.constructorTag formula leftTerm rightTerm ::ᵥ nil) args (fun i => by
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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.DispatcherProof
