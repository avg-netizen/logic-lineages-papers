module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open LiteralRawMP.ConstructorSupportProof
theorem internalLine : Targets.InternalLine := by
 intro n p qtag ptag ctag atag hq hp hc ha ctx left right
 let values := left ::ᵥ right ::ᵥ nil
 have hl : Computes p (.projection (0 : Fin 2)) values left := projection p values 0
 have hr : Computes p (.projection (1 : Fin 2)) values right := projection p values 1
 have hz := constantValue p values 0
 have hone := constantValue p values 1
 have htwo := constantValue p values 2
 have hthree := constantValue p values 3
 have hs := binary p values HistoryCodec.cons ctag hc _ _ _ _ htwo hr
 have harg := binary p values HistoryAppend.append atag ha _ _ _ _ hl hs
 have hadd := binary p values HistoryCodec.cons ctag hc _ _ _ _ hthree harg
 have hab := binary p values HistoryAppend.append atag ha _ _ _ _ hl hr
 have hsum := binary p values HistoryCodec.cons ctag hc _ _ _ _ hthree hab
 have hsucc := binary p values HistoryCodec.cons ctag hc _ _ _ _ htwo hsum
 have happ := binary p values HistoryAppend.append atag ha _ _ _ _ hadd hsucc
 have heq := binary p values HistoryCodec.cons ctag hc _ _ _ _ hz happ
 have hlast := binary p values HistoryCodec.cons ctag hc _ _ _ _ hr hz
 have hargsList := binary p values HistoryCodec.cons ctag hc _ _ _ _ hl hlast
 have hrefs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hz
 have hargs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hargsList hrefs
 have hpay := binary p values HistoryCodec.pair ptag hp _ _ _ _ hthree hargs
 have hrule := binary p values HistoryCodec.pair ptag hp _ _ _ _ hone hpay
 have hconclusion := binary p values HistoryCodec.pair ptag hp _ _ _ _ heq hrule
 exact binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hconclusion qtag hq

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ConstructorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ConstructorProof.internalLine
