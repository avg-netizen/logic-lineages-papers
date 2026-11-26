module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationEquationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.TickProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof

theorem tickNil {n ctx : Nat} (p : Program n) (ptag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (state : Term ctx) :
 Computes p [] tick (HistoryKernel.pairCall ptag .zero state ::ᵥ nil)
  (HistoryKernel.pairCall ptag .zero state) := by
 let args := HistoryKernel.pairCall ptag .zero state ::ᵥ nil
 exact chooseZero p [] args remaining (.projection 0) _ _
  (decoder p [] ptag hp false .zero state) (projection p [] args 0)

theorem tickCons {n ctx : Nat} (p : Program n) (ptag ctag stag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (token raw state : Term ctx) :
 Computes p [] tick
  (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag token raw) state ::ᵥ nil)
  (HistoryKernel.pairCall ptag raw (LiteralSyntaxStep.stepCall stag state token)) := by
 let row := HistoryLookup.consCall ctag token raw
 let args := HistoryKernel.pairCall ptag row state ::ᵥ nil
 have hrem : Computes p [] remaining args row := decoder p [] ptag hp false row state
 have hstate : Computes p [] taskState args state := decoder p [] ptag hp true row state
 have htail := unary p [] args HistoryLookup.tail remaining row raw hrem (tailCons p [] ctag hc token raw)
 have hhead := unary p [] args HistoryLookup.head remaining row token hrem (headCons p [] ctag hc token raw)
 have hstep := binary p [] args LiteralSyntaxStep.stepCode taskState (applyOne HistoryLookup.head remaining)
  state token (LiteralSyntaxStep.stepCall stag state token) hstate hhead
  (copies p [] LiteralSyntaxStep.stepCode stag hs _)
 have hout := binary p [] args HistoryCodec.pair (applyOne HistoryLookup.tail remaining)
  (applyTwo LiteralSyntaxStep.stepCode taskState (applyOne HistoryLookup.head remaining))
  raw (LiteralSyntaxStep.stepCall stag state token) _ htail hstep
  (copies p [] HistoryCodec.pair ptag hp _)
 let cp := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let pv := HistoryKernel.pairCall cp token raw
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx token raw
 have hpositive : Computes p [] remaining args (.succ pv) :=
  changeValue p [] remaining args row _ hrem (.base hcons)
 exact choosePositive p [] args remaining (.projection 0) _ pv _ hpositive hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.TickProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.TickProof
