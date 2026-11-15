module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.DecoderProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open TwoSol20261113.ReflexivityRecognizer
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
/-- Original payload/pair/list destructors recover BOTH runtime raw arguments
from the literal original line. No constructor tag or reference is dropped. -/
theorem arguments {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (caseTag predTag ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (formula leftTerm rightTerm : Term ctx) :
 Computes p G termCode (lineValue caseTag predTag ptag ctag formula leftTerm rightTerm ::ᵥ nil) formula ∧
 Computes p G RawAddSucc.secondTermCode (lineValue caseTag predTag ptag ctag formula leftTerm rightTerm ::ᵥ nil) leftTerm ∧
 Computes p G thirdTermCode (lineValue caseTag predTag ptag ctag formula leftTerm rightTerm ::ᵥ nil) rightTerm := by
 let concl := conclusionValue caseTag predTag ctag formula leftTerm rightTerm
 let thirdArg := HistoryLookup.consCall ctag rightTerm .zero
 let lastArg := HistoryLookup.consCall ctag leftTerm thirdArg
 let twoArgs := HistoryLookup.consCall ctag formula lastArg
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let pairArgs := HistoryKernel.pairCall ptag twoArgs refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 12) pairArgs
 let rule := HistoryKernel.pairCall ptag (.zero : Term ctx) payload
 let body := HistoryKernel.pairCall ptag concl rule
 let outLine := lineValue caseTag predTag ptag ctag formula leftTerm rightTerm
 let av := outLine ::ᵥ nil
 have hline : Computes p G (.projection 0) av (HistoryKernel.pairCall ptag .zero body) := projection p G av 0
 have hbody := RawReflexivity.LogicalProof.decoded p G ptag hp av (.projection 0) true .zero body hline
 have hrule := RawReflexivity.LogicalProof.decoded p G ptag hp av (right (.projection 0)) true concl rule hbody
 have hpay := RawReflexivity.LogicalProof.decoded p G ptag hp av (right (right (.projection 0))) true .zero payload hrule
 have hpair := RawReflexivity.LogicalProof.decoded p G ptag hp av (right (right (right (.projection 0)))) true (Term.numeral 12) pairArgs hpay
 have htwo : Computes p G argsCode av twoArgs :=
  RawReflexivity.LogicalProof.decoded p G ptag hp av (right (right (right (right (.projection 0))))) false twoArgs refs hpair
 have hfirst : Computes p G HistoryLookup.head (twoArgs ::ᵥ nil) formula := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx formula lastArg
  exact ⟨.base h⟩
 have htail : Computes p G HistoryLookup.tail (twoArgs ::ᵥ nil) lastArg := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalTailCons n p tag ctag ht hc ctx formula lastArg
  exact ⟨.base h⟩
 have hsecond : Computes p G HistoryLookup.head (lastArg ::ᵥ nil) leftTerm := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx leftTerm thirdArg
  exact ⟨.base h⟩
 have hlast := unary p G av HistoryLookup.tail argsCode twoArgs lastArg htwo htail
 have htail2 : Computes p G HistoryLookup.tail (lastArg ::ᵥ nil) thirdArg := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalTailCons n p tag ctag ht hc ctx leftTerm thirdArg
  exact ⟨.base h⟩
 have hthird : Computes p G HistoryLookup.head (thirdArg ::ᵥ nil) rightTerm := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx rightTerm .zero
  exact ⟨.base h⟩
 have hlast2 := unary p G av HistoryLookup.tail _ lastArg thirdArg hlast htail2
 exact ⟨unary p G av HistoryLookup.head argsCode twoArgs formula htwo hfirst,
  unary p G av HistoryLookup.head _ lastArg leftTerm hlast hsecond,
  unary p G av HistoryLookup.head _ thirdArg rightTerm hlast2 hthird⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.DecoderProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.DecoderProof
