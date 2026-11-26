module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.TermScanProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierNodesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.TermScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep LiteralSyntaxStep.ExpansionSupportProof
open SixSol20261112.Fuel NamedArithmeticGraph

open LiteralNumeralPrefix LiteralNumeralPrefix.TermScanProof

theorem universalExpand {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (termTask ptag binder) (Term.numeral 5))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) .zero)))) := by
 let args := termTask ptag binder ::ᵥ Term.numeral 5 ::ᵥ nil
 obtain ⟨hk,hn⟩ := termFields p [] ptag hp binder 5
 have ht : Computes p [] (.projection 1) args (Term.numeral 5) := projection p [] args 1
 have hout := successValue p [] args _ _ (singletonValue p [] args ctag hc _ _
  (taskValue p [] args ptag hp 0 LiteralSyntaxStep.context binder hn))
 have hex : Computes p [] expandCode args (.succ (HistoryLookup.consCall ctag (termTask ptag binder) .zero)) := by
  apply whenEq p [] args _ _ _ 0 _ hk
  apply whenNe p [] args _ _ _ 5 0 _ (by decide) ht
  apply whenNe p [] args _ _ _ 5 1 _ (by decide) ht
  apply whenNe p [] args _ _ _ 5 2 _ (by decide) ht
  exact whenEq p [] args _ _ _ 5 _ ht hout
 obtain ⟨h⟩ := hex etag he
 exact ⟨Hilbert.Local.finish h⟩

theorem universalStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (Term.numeral 5))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) rest)))) := by
 obtain ⟨hex⟩ := universalExpand p etag ptag ctag he hp hc binder
 obtain ⟨hst⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (termTask ptag binder) rest (Term.numeral 5) (HistoryLookup.consCall ctag (termTask ptag binder) .zero)
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) .zero rest
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 have heq := Logic.trans _ _ _ hcons (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ rest (.logical (.reflexive _)) hnil)
 exact ⟨Logic.trans _ _ _ (.mp hst hex) (Logic.unary (.succ (.var 0)) _ _ heq)⟩

theorem scanUniversal {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryLookup.consCall ctag (Term.numeral 5) raw))
   (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest) raw))) := by
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stepTag hstep
 obtain ⟨atag,ha⟩ := LiteralSyntaxValidator.QuantifierNodesProof.appendInstalled p stepTag hstep
 obtain ⟨hsucc⟩ := universalStep p stepTag etag atag ptag ctag hstep he ha hp hc binder rest
 obtain ⟨hunroll⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.scanConsSuccess p stag itag ltag ptag rtag ctag stepTag hs hi hl hp hr hc hstep
  (HistoryLookup.consCall ctag (termTask ptag binder) rest) (HistoryLookup.consCall ctag (termTask ptag binder) rest) (Term.numeral 5) raw
 exact ⟨.mp hunroll hsucc⟩

theorem addExpand {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (termTask ptag binder) (Term.numeral 3))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))))) := by
 let args := termTask ptag binder ::ᵥ Term.numeral 3 ::ᵥ nil
 obtain ⟨hk,hn⟩ := termFields p [] ptag hp binder 3
 have ht : Computes p [] (.projection 1) args (Term.numeral 3) := projection p [] args 1
 have hout := successValue p [] args _ _ (doubleValue p [] args ctag hc _ _
  (taskValue p [] args ptag hp 0 LiteralSyntaxStep.context binder hn))
 have hex : Computes p [] expandCode args (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))) := by
  apply whenEq p [] args _ _ _ 0 _ hk
  apply whenNe p [] args _ _ _ 3 0 _ (by decide) ht
  apply whenNe p [] args _ _ _ 3 1 _ (by decide) ht
  apply whenNe p [] args _ _ _ 3 2 _ (by decide) ht
  apply whenNe p [] args _ _ _ 3 5 _ (by decide) ht
  exact whenEq p [] args _ _ _ 3 _ ht hout
 obtain ⟨h⟩ := hex etag he
 exact ⟨Hilbert.Local.finish h⟩

theorem addStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (Term.numeral 3))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest))))) := by
 obtain ⟨hex⟩ := addExpand p etag ptag ctag he hp hc binder
 obtain ⟨hst⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (termTask ptag binder) rest (Term.numeral 3) (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))
 obtain ⟨houter⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero) rest
 obtain ⟨hinner⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) .zero rest
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 have hi := Logic.trans _ _ _ hinner (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ rest (.logical (.reflexive _)) hnil)
 have heq := Logic.trans _ _ _ houter (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ _ (.logical (.reflexive _)) hi)
 exact ⟨Logic.trans _ _ _ (.mp hst hex) (Logic.unary (.succ (.var 0)) _ _ heq)⟩

theorem scanAdd {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryLookup.consCall ctag (Term.numeral 3) raw))
   (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest)) raw))) := by
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stepTag hstep
 obtain ⟨atag,ha⟩ := LiteralSyntaxValidator.QuantifierNodesProof.appendInstalled p stepTag hstep
 obtain ⟨hsucc⟩ := addStep p stepTag etag atag ptag ctag hstep he ha hp hc binder rest
 obtain ⟨hunroll⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.scanConsSuccess p stag itag ltag ptag rtag ctag stepTag hs hi hl hp hr hc hstep
  (HistoryLookup.consCall ctag (termTask ptag binder) rest) (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (Term.numeral 3) raw
 exact ⟨.mp hunroll hsucc⟩

theorem mulExpand {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (termTask ptag binder) (Term.numeral 4))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))))) := by
 let args := termTask ptag binder ::ᵥ Term.numeral 4 ::ᵥ nil
 obtain ⟨hk,hn⟩ := termFields p [] ptag hp binder 4
 have ht : Computes p [] (.projection 1) args (Term.numeral 4) := projection p [] args 1
 have hout := successValue p [] args _ _ (doubleValue p [] args ctag hc _ _
  (taskValue p [] args ptag hp 0 LiteralSyntaxStep.context binder hn))
 have hex : Computes p [] expandCode args (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))) := by
  apply whenEq p [] args _ _ _ 0 _ hk
  apply whenNe p [] args _ _ _ 4 0 _ (by decide) ht
  apply whenNe p [] args _ _ _ 4 1 _ (by decide) ht
  apply whenNe p [] args _ _ _ 4 2 _ (by decide) ht
  apply whenNe p [] args _ _ _ 4 5 _ (by decide) ht
  apply whenNe p [] args _ _ _ 4 3 _ (by decide) ht
  exact whenEq p [] args _ _ _ 4 _ ht hout
 obtain ⟨h⟩ := hex etag he
 exact ⟨Hilbert.Local.finish h⟩

theorem mulStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (Term.numeral 4))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest))))) := by
 obtain ⟨hex⟩ := mulExpand p etag ptag ctag he hp hc binder
 obtain ⟨hst⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (termTask ptag binder) rest (Term.numeral 4) (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero))
 obtain ⟨houter⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) .zero) rest
 obtain ⟨hinner⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) .zero rest
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 have hi := Logic.trans _ _ _ hinner (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ rest (.logical (.reflexive _)) hnil)
 have heq := Logic.trans _ _ _ houter (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ _ (.logical (.reflexive _)) hi)
 exact ⟨Logic.trans _ _ _ (.mp hst hex) (Logic.unary (.succ (.var 0)) _ _ heq)⟩

theorem scanMul {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryLookup.consCall ctag (Term.numeral 4) raw))
   (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest)) raw))) := by
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stepTag hstep
 obtain ⟨atag,ha⟩ := LiteralSyntaxValidator.QuantifierNodesProof.appendInstalled p stepTag hstep
 obtain ⟨hsucc⟩ := mulStep p stepTag etag atag ptag ctag hstep he ha hp hc binder rest
 obtain ⟨hunroll⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.scanConsSuccess p stag itag ltag ptag rtag ctag stepTag hs hi hl hp hr hc hstep
  (HistoryLookup.consCall ctag (termTask ptag binder) rest) (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (Term.numeral 4) raw
 exact ⟨.mp hunroll hsucc⟩

theorem scanUnary {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (token : Nat)
 (ht : token = 2 ∨ token = 5) (binder rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryLookup.consCall ctag (Term.numeral token) raw))
   (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest) raw))) := by
 rcases ht with rfl | rfl
 · exact LiteralNumeralPrefix.TermScanProof.scanSucc p stag ptag ctag hs hp hc binder rest raw
 · exact scanUniversal p stag ptag ctag hs hp hc binder rest raw

theorem scanBinary {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (token : Nat)
 (ht : token = 3 ∨ token = 4) (binder rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryLookup.consCall ctag (Term.numeral token) raw))
   (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) (HistoryLookup.consCall ctag (termTask ptag binder) rest)) raw))) := by
 rcases ht with rfl | rfl
 · exact scanAdd p stag ptag ctag hs hp hc binder rest raw
 · exact scanMul p stag ptag ctag hs hp hc binder rest raw

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.TermScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.TermScanProof
