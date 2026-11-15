module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.ConstructorProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.DecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.LogicalProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open TwoSol20261113.ReflexivityRecognizer

theorem rawAcceptanceImp {n ctx : Nat} (p : Program n) (old : Program 1)
 (ltag caseTag predTag ptag ctag fval vtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩)
 (hcase : (nodes p)[caseTag]? = some ⟨1,UniformClosedCase12.caseCode⟩)
 (hpred : (nodes p)[predTag]? = some ⟨1,HistoryCodec.predecessor⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩) (formula leftTerm rightTerm : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (guards fval vtag formula leftTerm rightTerm)
  (.equal (leafCall ltag (lineValue caseTag predTag ptag ctag formula leftTerm rightTerm)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let F := Formula.equal (LiteralSyntaxValidator.formulaCall fval (.succ .zero) formula) (.succ .zero)
 let V := RawReflexivityDispatcher.valid vtag leftTerm
 let W := RawReflexivityDispatcher.valid vtag rightTerm
 let A := guards fval vtag formula leftTerm rightTerm
 let G := [A]
 let outLine := lineValue caseTag predTag ptag ctag formula leftTerm rightTerm
 let av := outLine ::ᵥ nil
 have hh : Hilbert.Local T ctx G (.conj (.conj F V) W) := .hypothesis List.mem_cons_self
 have hFV := Hilbert.Local.mp (.base (.logical (.andLeft (.conj F V) W))) hh
 have hW := Hilbert.Local.mp (.base (.logical (.andRight (.conj F V) W))) hh
 have hF := Hilbert.Local.mp (.base (.logical (.andLeft F V))) hFV
 have hV := Hilbert.Local.mp (.base (.logical (.andRight F V))) hFV
 obtain ⟨hformula, hleft, hright⟩ := DecoderProof.arguments p G caseTag predTag ptag ctag hp hc formula leftTerm rightTerm
 have hrebuilt := ConstructorProof.lineAt p G caseTag predTag ptag ctag hcase hpred hp hc
  termCode RawAddSucc.secondTermCode thirdTermCode av formula leftTerm rightTerm hformula hleft hright
 have hmatch := binary p G av equalCode (.projection 0) (line termCode RawAddSucc.secondTermCode thirdTermCode)
  outLine outLine (.succ .zero) (projection p G av 0) hrebuilt (equalDiagonal p G outLine)
 have hvalidFormula : Computes p G LiteralSyntaxValidator.formulaValidator
   ((.succ .zero) ::ᵥ formula ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag fval 2
   LiteralSyntaxValidator.formulaValidator ht hf ctx ((.succ .zero) ::ᵥ formula ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hF⟩
 have hvalidTerm : Computes p G termValidator (leftTerm ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1
   termValidator ht hv ctx (leftTerm ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hV⟩
 have hvalidRight : Computes p G termValidator (rightTerm ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1
   termValidator ht hv ctx (rightTerm ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hW⟩
 have hformulaGuard := binary p G av LiteralSyntaxValidator.formulaValidator (constant 1 1) termCode
  (.succ .zero) formula (.succ .zero) (constantValue p G av 1) hformula hvalidFormula
 have htermGuard := unary p G av termValidator RawAddSucc.secondTermCode leftTerm (.succ .zero)
  hleft hvalidTerm
 have hrightGuard := unary p G av termValidator thirdTermCode rightTerm (.succ .zero) hright hvalidRight
 have hterms := choosePositive p G av _ (constant 1 0) _ .zero (.succ .zero) htermGuard hrightGuard
 have hguards := choosePositive p G av _ (constant 1 0) _ .zero (.succ .zero) hformulaGuard hterms
 have hrecognizer : Computes p G recognizer av (.succ .zero) :=
  choosePositive p G av _ _ _ .zero (.succ .zero) hmatch hguards
 obtain ⟨hout⟩ := choosePositive p G av recognizer (UniformClosedRule13.logicalLeaf old) (constant 1 1) .zero (.succ .zero)
  hrecognizer (constantValue p G av 1) ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

theorem exactInternalLogical : Targets.InternalLogical := by
 intro n p old qtag ltag caseTag predTag ptag ctag fval vtag hq hl hcase hpred hp hc hf hv ctx formula leftTerm rightTerm
 obtain ⟨hline⟩ := ConstructorProof.exactInternalLine n p qtag caseTag predTag ptag ctag hq hcase hpred hp hc ctx formula leftTerm rightTerm
 obtain ⟨haccept⟩ := rawAcceptanceImp p old ltag caseTag predTag ptag ctag fval vtag hl hcase hpred hp hc hf hv formula leftTerm rightTerm
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 let T := GorbowPRNumeralCalculation.Theory p
 let A := guards fval vtag formula leftTerm rightTerm
 have hA : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (.base haccept) hA
 have hout := localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.LogicalProof
