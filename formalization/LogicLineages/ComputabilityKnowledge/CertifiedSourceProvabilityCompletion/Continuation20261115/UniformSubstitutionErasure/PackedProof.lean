module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.PackedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LogicProof
theorem positive {n ctx : Nat} (p : Program n) (etag ntag otag ptag ctag stag emitTag atag htag ttag : Nat)
 (he : (nodes p)[etag]? = some ⟨1,eraseCode⟩)
 (hn : (nodes p)[ntag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (ho : (nodes p)[otag]? = some ⟨1,LiteralSyntaxScan.tick⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hm : (nodes p)[emitTag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (code state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (packedProperty etag ntag otag ptag (.succ code) state out raw)) := by
 obtain ⟨hreconstruct⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag htag ttag hc hh ht ctx code
 obtain ⟨hcons⟩ := TickCasesProof.consCase p etag ntag otag ptag ctag stag emitTag atag
  he hn ho hp hc hs hm ha (call htag (.succ code ::ᵥ nil)) (call ttag (.succ code ::ᵥ nil)) state out raw
 exact ⟨.mp (.mp (transportPacked etag ntag otag ptag _ _ state out raw) hreconstruct) hcons⟩
theorem arbitraryTokens {n ctx : Nat} (p : Program n) (etag ntag otag ptag ctag stag emitTag atag htag ttag : Nat)
 (he : (nodes p)[etag]? = some ⟨1,eraseCode⟩)
 (hn : (nodes p)[ntag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (ho : (nodes p)[otag]? = some ⟨1,LiteralSyntaxScan.tick⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hm : (nodes p)[emitTag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (tokens state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (packedProperty etag ntag otag ptag tokens state out raw)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := packedProperty etag ntag otag ptag tokens state out raw
 let E := Formula.equal tokens .zero
 obtain ⟨hz⟩ := TickCasesProof.nilCase p etag ntag otag ptag he hn ho hp state out raw
 have he0 : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (transportPacked etag ntag otag ptag .zero tokens state out raw))
   (HistoryOrder.StepProof.localSym _ _ he0)) (.base hz)))
 let H := HistoryOrder.SupportProof.predBody tokens
 have hh0 : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm tokens) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hn0⟩ := positive p etag ntag otag ptag ctag stag emitTag atag htag ttag
  he hn ho hp hc hs hm ha hh ht (.var (0 : Fin (ctx+1))) (liftTerm state) (liftTerm out) (liftTerm raw)
 have hout := Hilbert.Local.mp (.mp (.base (transportPacked etag ntag otag ptag _ _
  (liftTerm state) (liftTerm out) (liftTerm raw))) (HistoryOrder.StepProof.localSym _ _ hh0)) (.base hn0)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,weakenPacked] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hp0⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T tokens
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hp0) hsplit⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.PackedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.PackedProof
