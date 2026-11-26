module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open LiteralRawMP.ConstructorSupportProof

theorem internalLine : Targets.InternalLine := by
 intro n p qtag ptag ctag atag hq hp hc ha ctx raw
 let values := raw ::ᵥ nil
 have hr : Computes p (.projection (0 : Fin 1)) values raw := projection p values 0
 have hz := constantValue p values 0
 have hone := constantValue p values 1
 have htwo := constantValue p values 2
 have hthree := constantValue p values 3
 have hzeroRaw := binary p values HistoryCodec.cons ctag hc _ _ _ _ hone hz
 have harg := binary p values HistoryAppend.append atag ha _ _ _ _ hr hzeroRaw
 have hadd := binary p values HistoryCodec.cons ctag hc _ _ _ _ hthree harg
 have happ := binary p values HistoryAppend.append atag ha _ _ _ _ hadd hr
 have heq := binary p values HistoryCodec.cons ctag hc _ _ _ _ hz happ
 have hs := binary p values HistoryCodec.cons ctag hc _ _ _ _ hr hz
 have hrefs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hz
 have hargs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hs hrefs
 have hpay := binary p values HistoryCodec.pair ptag hp _ _ _ _ htwo hargs
 have hrule := binary p values HistoryCodec.pair ptag hp _ _ _ _ hone hpay
 have hconclusion := binary p values HistoryCodec.pair ptag hp _ _ _ _ heq hrule
 exact binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hconclusion qtag hq
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ConstructorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ConstructorProof.internalLine
