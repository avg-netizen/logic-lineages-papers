module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportBoundProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralSyntaxScan.StateRecursionProof LiteralSyntaxScan.FusionAlgebraProof
/-- Exact cons recursion with an observed original step output, in local context. -/
theorem consAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (itag len ptag r ctag stag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (token raw tasks nextState : Term ctx)
 (hstep : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) token) nextState)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (scanState itag len ptag r (HistoryLookup.consCall ctag token raw) (.succ tasks))
   (scanState itag len ptag r raw nextState))) := by
 obtain ⟨hcns⟩ := LiteralSyntaxScan.StateRecursionProof.cons p itag len ptag r ctag stag hi hlen hp hc hs token raw (.succ tasks)
 have htail := scanCongruence itag len ptag r raw raw _ nextState (.base (.logical (.reflexive raw))) hstep
 exact ⟨localTrans _ _ _ (.base hcns) htail⟩
/-- Successful cons scan cannot have a rejected first step: original noneAll
propagates zero through the actual tail iterator. -/
theorem rejectZero {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (itag len ptag r atag ctag stag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (token raw tasks result : Term ctx) (Q : Formula ctx)
 (hz : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) token) .zero))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (scanState itag len ptag r (HistoryLookup.consCall ctag token raw) (.succ tasks)) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G Q) := by
 obtain ⟨hcns⟩ := consAt p G itag len ptag r ctag stag hi hlen hp hc hs token raw tasks .zero hz
 obtain ⟨hnone⟩ := LiteralSyntaxScan.NoneInductionProof.noneAll p itag len ptag r atag ctag stag hi hlen hp hr ha hc hs raw
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hold) (localTrans _ _ _ hcns (.base hnone))
 exact ⟨Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero result)))⟩
/-- Genuine tail induction composition with both internal intermediate witnesses
exposed. Subsequent binder elimination, not an external premise, supplies them. -/
theorem positiveAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (itag len ptag q l r ctag stag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (token raw ot nt result oldNext newNext : Term ctx)
 (hih : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (ScanStateTransportBoundProof.allStacks itag len ptag q l r raw))
 (hrel : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r oldNext newNext))
 (ho : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ ot) token) (.succ oldNext)))
 (hn : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ nt) token) (.succ newNext)))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (scanState itag len ptag r (HistoryLookup.consCall ctag token raw) (.succ ot)) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (ScanStateTransportTargets.witnesses itag len ptag q l r (HistoryLookup.consCall ctag token raw) nt result)) := by
 obtain ⟨hoc⟩ := consAt p G itag len ptag r ctag stag hi hlen hp hc hs token raw ot (.succ oldNext) ho
 obtain ⟨hnc⟩ := consAt p G itag len ptag r ctag stag hi hlen hp hc hs token raw nt (.succ newNext) hn
 have htail := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hoc) hold
 have hinst := Hilbert.Local.mp (.base (ScanStateTransportBoundProof.instanceRule itag len ptag q l r raw oldNext newNext result)) hih
 have hres := Hilbert.Local.mp (.mp hinst hrel) htail
 obtain ⟨htransfer⟩ := ScanStateTransportWitnessProof.transfer (T := GorbowPRNumeralCalculation.Theory p)
  itag len ptag q l r (HistoryLookup.consCall ctag token raw) nt raw newNext result
 exact ⟨.mp (.mp (.base htransfer) hres) hnc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportConsProof
