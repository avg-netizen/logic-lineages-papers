module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.TermScanProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierNodesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.TermScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep LiteralSyntaxStep.ExpansionSupportProof
open SixSol20261112.Fuel NamedArithmeticGraph

open LiteralNumeralPrefix LiteralNumeralPrefix.TermScanProof

theorem equalityExpand {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (taskCall ptag 1 binder) (Term.numeral 0))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 0 ::ᵥ nil
 obtain ⟨hk,hn⟩ := taskFields p [] ptag hp binder 0
 have ht : Computes p [] (.projection 1) args (Term.numeral 0) := projection p [] args 1
 have hout := successValue p [] args _ _ (doubleValue p [] args ctag hc _ _
  (taskValue p [] args ptag hp 0 LiteralSyntaxStep.context binder hn))
 have hex : Computes p [] expandCode args (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))) := by
  apply whenNe p [] args _ _ _ 1 0 _ (by decide) hk
  apply whenEq p [] args _ _ _ 1 _ hk
  exact whenEq p [] args _ _ _ 0 _ ht hout
 obtain ⟨h⟩ := hex etag he
 exact ⟨Hilbert.Local.finish h⟩

theorem equalityStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag (taskCall ptag 1 binder) rest)) (Term.numeral 0))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest))))) := by
 obtain ⟨hex⟩ := equalityExpand p etag ptag ctag he hp hc binder
 obtain ⟨hst⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (taskCall ptag 1 binder) rest (Term.numeral 0) (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))
 obtain ⟨houter⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero) rest
 obtain ⟨hinner⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) .zero rest
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 have hi := Logic.trans _ _ _ hinner (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ rest (.logical (.reflexive _)) hnil)
 have heq := Logic.trans _ _ _ houter (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ _ (.logical (.reflexive _)) hi)
 exact ⟨Logic.trans _ _ _ (.mp hst hex) (Logic.unary (.succ (.var 0)) _ _ heq)⟩

theorem scanEquality {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (taskCall ptag 1 binder) rest)
   (HistoryLookup.consCall ctag (Term.numeral 0) raw))
   (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest)) raw))) := by
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stepTag hstep
 obtain ⟨atag,ha⟩ := LiteralSyntaxValidator.QuantifierNodesProof.appendInstalled p stepTag hstep
 obtain ⟨hsucc⟩ := equalityStep p stepTag etag atag ptag ctag hstep he ha hp hc binder rest
 obtain ⟨hunroll⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.scanConsSuccess p stag itag ltag ptag rtag ctag stepTag hs hi hl hp hr hc hstep
  (HistoryLookup.consCall ctag (taskCall ptag 1 binder) rest) (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (Term.numeral 0) raw
 exact ⟨.mp hunroll hsucc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.TermScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.TermScanProof
