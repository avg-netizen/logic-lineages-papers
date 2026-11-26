module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open TwoSol20261113.ReflexivityRecognizer LiteralRawMP.ConstructorSupportProof

theorem nativeLine : Targets.NativeLine := by
 intro raw
 exact NativeProof.reflexiveLineEval (.projection 0) (Encodable.encode raw ::ᵥ nil) raw rfl

theorem internalLine : Targets.InternalLine := by
 intro n p qtag ptag ctag atag hq hp hc ha ctx raw
 let values := raw ::ᵥ nil
 have hr : Computes p (.projection (0 : Fin 1)) values raw := projection p values 0
 have hz := constantValue p values 0
 have h11 := constantValue p values 11
 have happ := binary p values HistoryAppend.append atag ha _ _ _ _ hr hr
 have heq := binary p values HistoryCodec.cons ctag hc _ _ _ _ hz happ
 have hs := binary p values HistoryCodec.cons ctag hc _ _ _ _ hr hz
 have hrefs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hz
 have hargs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hs hrefs
 have hpay := binary p values HistoryCodec.pair ptag hp _ _ _ _ h11 hargs
 have hrule := binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hpay
 have hconclusion := binary p values HistoryCodec.pair ptag hp _ _ _ _ heq hrule
 exact binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hconclusion qtag hq
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.ConstructorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.ConstructorProof.nativeLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.ConstructorProof.internalLine
