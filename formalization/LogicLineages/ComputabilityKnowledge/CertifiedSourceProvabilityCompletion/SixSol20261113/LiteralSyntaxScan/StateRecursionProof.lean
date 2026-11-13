module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.TickProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationFirstProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.StateRecursionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport Iteration IterationEquationsProof

def scanState {ctx : Nat} (itag ltag ptag rtag : Nat) (raw state : Term ctx) : Term ctx :=
 call rtag (runCall itag (HistoryLengthOffset.lengthCall ltag raw)
  (HistoryKernel.pairCall ptag raw state) ::ᵥ nil)

theorem nil {n ctx : Nat} (p : Program n) (itag ltag ptag rtag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (scanState itag ltag ptag rtag .zero state) state)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 obtain ⟨hz⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p ltag hl ctx
 have hlen := HistoryAppend.PositiveProof.binaryCongruence (T := T) itag _ .zero
  (HistoryKernel.pairCall ptag .zero state) (HistoryKernel.pairCall ptag .zero state)
  hz (.logical (.reflexive _))
 obtain ⟨hi0⟩ := IterationEquationsProof.zero p itag hi (HistoryKernel.pairCall ptag .zero state)
 obtain ⟨hd⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp (.zero : Term ctx) state
 exact ⟨Logic.trans _ _ _
  (HistoryLookup.DestructorProof.unaryCallCongruence rtag _ _ (Logic.trans _ _ _ hlen hi0)) hd⟩

theorem cons {n ctx : Nat} (p : Program n) (itag ltag ptag rtag ctag stag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (token raw state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (scanState itag ltag ptag rtag (HistoryLookup.consCall ctag token raw) state)
    (scanState itag ltag ptag rtag raw (LiteralSyntaxStep.stepCall stag state token)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let row := HistoryLookup.consCall ctag token raw
 let initial := HistoryKernel.pairCall ptag row state
 let len := HistoryLengthOffset.lengthCall ltag raw
 obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx token raw
 have hcount := HistoryAppend.PositiveProof.binaryCongruence (T := T) itag _ (.succ len)
  initial initial hlen (.logical (.reflexive initial))
 obtain ⟨hfirst⟩ := IterationFirstProof.internalFirst p itag hi len initial
 obtain ⟨htick⟩ := TickProof.tickCons p ptag ctag stag hp hc hs token raw state
  (tickTag itag) (tickInstalled p itag hi)
 have hstate := HistoryAppend.PositiveProof.binaryCongruence (T := T) itag len len _ _
  (.logical (.reflexive len)) (Hilbert.Local.finish htick)
 exact ⟨HistoryLookup.DestructorProof.unaryCallCongruence rtag _ _
  (Logic.trans _ _ _ hcount (Logic.trans _ _ _ hfirst hstate))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.StateRecursionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.StateRecursionProof
