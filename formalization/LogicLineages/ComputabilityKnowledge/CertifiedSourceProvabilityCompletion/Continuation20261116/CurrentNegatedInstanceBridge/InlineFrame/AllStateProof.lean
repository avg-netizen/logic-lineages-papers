module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.AllStateProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LogicProof
theorem positive {n ctx : Nat} (p : Program n) (ptag atag ltag rtag ttag ctag stag etag htag tailtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ht : (nodes p)[ttag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (htail : (nodes p)[tailtag]? = some ⟨1,HistoryLookup.tail⟩) (prefixCode code state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (packedProperty ptag atag ltag rtag ttag prefixCode (.succ code) state out raw)) := by
 obtain ⟨hrec⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag htag tailtag hc hh htail ctx code
 obtain ⟨hcons⟩ := TickCasesProof.consCase p ptag atag ltag rtag ttag ctag stag etag
  hp ha hl hr ht hc hs he prefixCode (call htag (.succ code ::ᵥ nil)) (call tailtag (.succ code ::ᵥ nil)) state out raw
 exact ⟨.mp (.mp (transportPacked ptag atag ltag rtag ttag prefixCode _ _ state out raw) hrec) hcons⟩
theorem arbitraryTokens {n ctx : Nat} (p : Program n) (ptag atag ltag rtag ttag ctag stag etag htag tailtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ht : (nodes p)[ttag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (htail : (nodes p)[tailtag]? = some ⟨1,HistoryLookup.tail⟩) (prefixCode tokens state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (packedProperty ptag atag ltag rtag ttag prefixCode tokens state out raw)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := packedProperty ptag atag ltag rtag ttag prefixCode tokens state out raw
 let E := Formula.equal tokens .zero
 obtain ⟨hz⟩ := TickCasesProof.nilCase p ptag atag ltag rtag ttag hp ha hl hr ht prefixCode state out raw
 have he0 : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (transportPacked ptag atag ltag rtag ttag prefixCode .zero tokens state out raw))
   (HistoryOrder.StepProof.localSym _ _ he0)) (.base hz)))
 let H := HistoryOrder.SupportProof.predBody tokens
 have hh0 : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm tokens) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hn⟩ := positive p ptag atag ltag rtag ttag ctag stag etag htag tailtag
  hp ha hl hr ht hc hs he hh htail (liftTerm prefixCode) (.var (0 : Fin (ctx+1))) (liftTerm state) (liftTerm out) (liftTerm raw)
 have hout := Hilbert.Local.mp (.mp (.base (transportPacked ptag atag ltag rtag ttag (liftTerm prefixCode) _ _
  (liftTerm state) (liftTerm out) (liftTerm raw))) (HistoryOrder.StepProof.localSym _ _ hh0)) (.base hn)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,weakenPacked] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hp0⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T tokens
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hp0) hsplit⟩
theorem arbitraryState {n ctx : Nat} (p : Program n) (ptag atag ltag rtag ttag ctag stag etag htag tailtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ht : (nodes p)[ttag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (htail : (nodes p)[tailtag]? = some ⟨1,HistoryLookup.tail⟩) (prefixCode packed raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property ptag atag ltag rtag ttag prefixCode packed raw)) := by
 obtain ⟨hrec⟩ := UniformSubstitutionErasure.AtomsProof.reconstruct p ptag ltag rtag hp hl hr packed
 obtain ⟨hpacked⟩ := arbitraryTokens p ptag atag ltag rtag ttag ctag stag etag htag tailtag
  hp ha hl hr ht hc hs he hh htail prefixCode (call ltag (packed ::ᵥ nil))
  (call ltag (call rtag (packed ::ᵥ nil) ::ᵥ nil)) (call rtag (call rtag (packed ::ᵥ nil) ::ᵥ nil)) raw
 exact ⟨.mp (.mp (transport ptag atag ltag rtag ttag prefixCode _ packed raw) hrec) hpacked⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.AllStateProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.AllStateProof
