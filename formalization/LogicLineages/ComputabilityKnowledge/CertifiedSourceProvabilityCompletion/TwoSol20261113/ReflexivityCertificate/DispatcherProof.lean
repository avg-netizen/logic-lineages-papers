module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

def payload {ctx : Nat} (ptag ctag : Nat) (term : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag (Term.numeral 11)
  (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag term .zero)
   (HistoryKernel.pairCall ptag .zero .zero)))

theorem quoteEquation {k n ctx : Nat} (t : Term k) (old arithmetic : Program 1) (x : Program 3)
 (p : Program n) (I : Installation p t old arithmetic x) (values : List.Vector (Term ctx) k) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (line I.qtag values) (HistoryKernel.pairCall I.ptag .zero
   (HistoryKernel.pairCall I.ptag (raw I.etag values)
    (payload I.ptag I.ctag (LiteralTemplateQuote.quoteCall I.ttag values)))))) :=
 LiteralReflexivityQuote.LineInternalProof.internalEquation k t n p I.qtag I.etag I.ttag I.ptag I.ctag
  I.hq I.he I.ht I.hp I.hc ctx values

theorem valueAt {n arity ctx : Nat} (p : Program n) (q : Program arity) (qtag : Nat)
 (hq : (nodes p)[qtag]? = some ⟨arity,q⟩) (args : List.Vector (Term ctx) arity) (value : Term ctx)
 (he : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call qtag args) value))) :
 Computes p [] q args value := by
 intro tag ht
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag qtag arity q ht hq ctx args
 obtain ⟨h⟩ := he
 exact ⟨.base (Logic.trans _ _ _ hcopy h)⟩

theorem directValidity {k n ctx : Nat} (t : Term k) (old arithmetic : Program 1) (x : Program 3)
 (p : Program n) (I : Installation p t old arithmetic x) (values : List.Vector (Term ctx) k) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxValidator.lineCall I.ltag (HistoryKernel.pairCall I.ptag .zero
   (HistoryKernel.pairCall I.ptag (raw I.etag values)
    (payload I.ptag I.ctag (LiteralTemplateQuote.quoteCall I.ttag values))))) (.succ .zero))) := by
 obtain ⟨hb⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding n p I.ltag I.ftag I.ptag
  I.hl I.hf I.hp ctx .zero (raw I.etag values)
  (payload I.ptag I.ctag (LiteralTemplateQuote.quoteCall I.ttag values))
 obtain ⟨hv⟩ := LiteralEqualityQuote.ValidatorProof.internalValidator k t t n p I.etag I.ftag
  I.he I.hf ctx values .zero
 exact ⟨Logic.trans _ _ _ hb hv⟩

theorem internalDispatcher : Targets.InternalDispatcher := by
 intro k t old arithmetic x n p I ctx values index fuel history
 let T := GorbowPRNumeralCalculation.Theory p
 let rawEq := raw I.etag values
 let tail := payload I.ptag I.ctag (LiteralTemplateQuote.quoteCall I.ttag values)
 let ruleRest := HistoryKernel.pairCall I.ptag (Term.numeral 11)
  (HistoryKernel.pairCall I.ptag (HistoryLookup.consCall I.ctag (LiteralTemplateQuote.quoteCall I.ttag values) .zero)
   (HistoryKernel.pairCall I.ptag .zero .zero))
 let expanded := HistoryKernel.pairCall I.ptag .zero (HistoryKernel.pairCall I.ptag rawEq tail)
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ expanded ::ᵥ nil
 obtain ⟨hq⟩ := quoteEquation t old arithmetic x p I values
 obtain ⟨hlog⟩ := ReflexivityRecognizer.LogicalInternalProof.internalLogical k t old n p
  I.btag I.qtag I.etag I.ttag I.ptag I.ctag I.atag I.vtag
  I.hb I.hq I.he I.ht I.hp I.hc I.ha I.hv ctx values
 have hlogExpanded : Nonempty (Derivation T (.equal (ReflexivityRecognizer.leafCall I.btag expanded) (.succ .zero))) :=
  ⟨Logic.trans _ _ _ (Support.equalitySymmetry _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.btag _ _ hq)) hlog⟩
 have hvalid := directValidity t old arithmetic x p I values
 have hline : Computes p [] HistoryDispatcher.lineCode args expanded := projection p [] args 3
 have hr1 := ReflexivityRecognizer.LogicalInternalProof.decoded p I.ptag I.hp args HistoryDispatcher.lineCode true
  .zero (HistoryKernel.pairCall I.ptag rawEq tail) hline
 have hr2 := ReflexivityRecognizer.LogicalInternalProof.decoded p I.ptag I.hp args
  (HistoryDispatcher.right HistoryDispatcher.lineCode) true rawEq tail hr1
 have hrule : Computes p [] HistoryDispatcher.ruleCode args .zero :=
  ReflexivityRecognizer.LogicalInternalProof.decoded p I.ptag I.hp args
   (HistoryDispatcher.right (HistoryDispatcher.right HistoryDispatcher.lineCode)) false .zero ruleRest hr2
 have ht0 := binary p [] args equalCode HistoryDispatcher.ruleCode (constant 4 0) .zero .zero (.succ .zero)
  hrule (constantValue p [] args 0) (equalDiagonal p [] .zero)
 have hlogical := unary p [] args (logical old) HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p (logical old) I.btag I.hb (expanded ::ᵥ nil) (.succ .zero) hlogExpanded)
 have hrules : Computes p [] (HistoryDispatcher.ruleDispatcher (logical old) arithmetic x) args (.succ .zero) :=
  choosePositive p [] args _ _ _ .zero (.succ .zero) ht0 hlogical
 have hvalid' := unary p [] args validity HistoryDispatcher.lineCode expanded (.succ .zero) hline
  (valueAt p validity I.ltag I.hl (expanded ::ᵥ nil) (.succ .zero) hvalid)
 obtain ⟨hout⟩ := choosePositive p [] args _ _ _ .zero (.succ .zero) hvalid' hrules I.dtag I.hd
 have hcg := callCongruence (T := T) (G := []) I.dtag
  (index ::ᵥ fuel ::ᵥ history ::ᵥ line I.qtag values ::ᵥ nil) args (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive index))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive fuel))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive history))
       | succ i => cases i using Fin.cases with
         | zero => exact .base hq
         | succ i => exact Fin.elim0 i)
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ hcg hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.DispatcherProof
