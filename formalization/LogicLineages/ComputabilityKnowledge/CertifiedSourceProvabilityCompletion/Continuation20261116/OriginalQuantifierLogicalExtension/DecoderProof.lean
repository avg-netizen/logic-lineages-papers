module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.DecoderProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open OriginalQuantifierLogicalProducers
open TwoSol20261113.ReflexivityRecognizer
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem arguments {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (isExists : Bool) (ptag ctag atag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (a b : Term ctx) :
 Computes p G firstArg (lineValue isExists ptag ctag atag a b ::ᵥ nil) a ∧
 (isExists = false → Computes p G secondArg (lineValue isExists ptag ctag atag a b ::ᵥ nil) b) := by
 let concl := conclusionValue isExists ctag atag a b
 let lastArg := if isExists then (.zero : Term ctx) else HistoryLookup.consCall ctag b .zero
 let allArgs := HistoryLookup.consCall ctag a lastArg
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let pairArgs := HistoryKernel.pairCall ptag allArgs refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral (if isExists then 10 else 2)) pairArgs
 let rule := HistoryKernel.pairCall ptag (.zero : Term ctx) payload
 let body := HistoryKernel.pairCall ptag concl rule
 let av := lineValue isExists ptag ctag atag a b ::ᵥ nil
 have hline : Computes p G (.projection 0) av (HistoryKernel.pairCall ptag .zero body) := projection p G av 0
 have hbody := RawReflexivity.LogicalProof.decoded p G ptag hp av (.projection 0) true .zero body hline
 have hrule := RawReflexivity.LogicalProof.decoded p G ptag hp av (right (.projection 0)) true concl rule hbody
 have hpay := RawReflexivity.LogicalProof.decoded p G ptag hp av (right (right (.projection 0))) true .zero payload hrule
 have hpair := RawReflexivity.LogicalProof.decoded p G ptag hp av (right (right (right (.projection 0)))) true
  (Term.numeral (if isExists then 10 else 2)) pairArgs hpay
 have hall : Computes p G argsCode av allArgs :=
  RawReflexivity.LogicalProof.decoded p G ptag hp av (right (right (right (right (.projection 0))))) false allArgs refs hpair
 have hfirst : Computes p G HistoryLookup.head (allArgs ::ᵥ nil) a := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx a lastArg
  exact ⟨.base h⟩
 refine ⟨unary p G av HistoryLookup.head argsCode allArgs a hall hfirst,?_⟩
 intro hs
 subst isExists
 have htail : Computes p G HistoryLookup.tail (allArgs ::ᵥ nil) lastArg := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalTailCons n p tag ctag ht hc ctx a lastArg
  exact ⟨.base h⟩
 have hsecond : Computes p G HistoryLookup.head (lastArg ::ᵥ nil) b := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx b .zero
  exact ⟨.base h⟩
 have hlast := unary p G av HistoryLookup.tail argsCode allArgs lastArg hall htail
 exact unary p G av HistoryLookup.head _ lastArg b hlast hsecond

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.DecoderProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.DecoderProof
