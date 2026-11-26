module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportIndexProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Original index expansion with its positive runtime difference witness gives
an actual step returning the unmodified tail, not an assumed transfer equation. -/
theorem indexStep {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (stag etag ctag atag dtag l r : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (head tail tok gap : Term ctx)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (head ::ᵥ nil)) (Term.numeral 2)))
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag tok (call r (head ::ᵥ nil))) (.succ gap))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag head tail)) tok) (.succ tail))) := by
 obtain ⟨hex⟩ := ExpansionRuntimeProof.indexPositive p G l r dtag hl hr hd head tok gap hk hg etag he
 obtain ⟨hstep⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx head tail tok .zero
 have hresult := Hilbert.Local.mp (.base hstep) hex
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx tail
 have hsucc := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (gamma := G) hnil)
 have hsucc' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (.succ (HistoryAppend.appendCall atag .zero tail)) (.succ tail)) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hsucc
 exact ⟨localTrans _ _ _ hresult hsucc'⟩
/-- The positive index branch at arbitrary raw heads, once its two internal gap
witnesses have been exposed. Later existential elimination supplies these witnesses. -/
theorem positiveTransport {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (stag etag ctag atag dtag len q l r : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nh nt tok result og ng : Term ctx)
 (hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (taskRelation l r oh nh))
 (htail : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r ot nt))
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (oh ::ᵥ nil)) (Term.numeral 2)))
 (hog : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag tok (call r (oh ::ᵥ nil))) (.succ og)))
 (hng : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag tok (call r (nh ::ᵥ nil))) (.succ ng)))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (StepTransportTargets.witnesses stag len q l r (HistoryLookup.consCall ctag nh nt) tok result)) := by
 have hkind := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hnk := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hkind) hk
 obtain ⟨ho⟩ := indexStep p G stag etag ctag atag dtag l r hs he hc ha hd hl hr oh ot tok og hk hog
 obtain ⟨hn⟩ := indexStep p G stag etag ctag atag dtag l r hs he hc ha hd hl hr nh nt tok ng hnk hng
 have heq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hold) ho
 have hresult := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) heq
 have hrel := Hilbert.Local.mp (.mp (.base (FinitePrefixProof.stackLeft len q l r ot result nt))
  (HistoryOrder.StepProof.localSym _ _ hresult)) htail
 have hw := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hn) hrel
 exact ⟨.mp (.base (StepTransportWitnessProof.witnessIntro stag len q l r
  (HistoryLookup.consCall ctag nh nt) tok result nt)) hw⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportIndexProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportIndexProof
