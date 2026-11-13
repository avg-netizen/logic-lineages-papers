module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierNodesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.TermScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep LiteralSyntaxStep.ExpansionSupportProof
open SixSol20261112.Fuel NamedArithmeticGraph

theorem termFields {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (binder : Term ctx) (token : Nat) :
 Computes p G kind (termTask ptag binder ::ᵥ Term.numeral token ::ᵥ nil) .zero ∧
 Computes p G LiteralSyntaxStep.context (termTask ptag binder ::ᵥ Term.numeral token ::ᵥ nil) binder := by
 let args := termTask ptag binder ::ᵥ Term.numeral token ::ᵥ nil
 exact ⟨unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _),
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)⟩

theorem zeroExpand {n ctx : Nat} (p : Program n) (etag ptag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (binder : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (termTask ptag binder) (.succ .zero)) (.succ .zero))) := by
 let args := termTask ptag binder ::ᵥ Term.numeral 1 ::ᵥ nil
 obtain ⟨hk,_⟩ := termFields p [] ptag hp binder 1
 have ht : Computes p [] (.projection 1) args (Term.numeral 1) := projection p [] args 1
 have hex : Computes p [] expandCode args (.succ .zero) := by
  apply whenEq p [] args _ _ _ 0 _ hk
  apply whenNe p [] args _ _ _ 1 0 _ (by decide) ht
  exact whenEq p [] args _ _ _ 1 _ ht (constantValue p [] args 1)
 obtain ⟨h⟩ := hex etag he
 exact ⟨Hilbert.Local.finish h⟩

theorem succExpand {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (termTask ptag binder) (.succ (.succ .zero)))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) .zero)))) := by
 let args := termTask ptag binder ::ᵥ Term.numeral 2 ::ᵥ nil
 obtain ⟨hk,hn⟩ := termFields p [] ptag hp binder 2
 have ht : Computes p [] (.projection 1) args (Term.numeral 2) := projection p [] args 1
 have hout := successValue p [] args _ _ (singletonValue p [] args ctag hc _ _
  (taskValue p [] args ptag hp 0 LiteralSyntaxStep.context binder hn))
 have hex : Computes p [] expandCode args (.succ (HistoryLookup.consCall ctag (termTask ptag binder) .zero)) := by
  apply whenEq p [] args _ _ _ 0 _ hk
  apply whenNe p [] args _ _ _ 2 0 _ (by decide) ht
  apply whenNe p [] args _ _ _ 2 1 _ (by decide) ht
  exact whenEq p [] args _ _ _ 2 _ ht hout
 obtain ⟨h⟩ := hex etag he
 exact ⟨Hilbert.Local.finish h⟩

theorem zeroStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (.succ .zero)) (.succ rest))) := by
 obtain ⟨hex⟩ := zeroExpand p etag ptag he hp binder
 obtain ⟨hst⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx (termTask ptag binder) rest (.succ .zero) .zero
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 exact ⟨Logic.trans _ _ _ (.mp hst hex) (Logic.unary (.succ (.var 0)) _ _ hnil)⟩

theorem succStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag (termTask ptag binder) rest)) (.succ (.succ .zero)))
   (.succ (HistoryLookup.consCall ctag (termTask ptag binder) rest)))) := by
 obtain ⟨hex⟩ := succExpand p etag ptag ctag he hp hc binder
 obtain ⟨hst⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (termTask ptag binder) rest (.succ (.succ .zero)) (HistoryLookup.consCall ctag (termTask ptag binder) .zero)
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (termTask ptag binder) .zero rest
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 have heq := Logic.trans _ _ _ hcons (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ rest (.logical (.reflexive _)) hnil)
 exact ⟨Logic.trans _ _ _ (.mp hst hex) (Logic.unary (.succ (.var 0)) _ _ heq)⟩

theorem scanZero {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryLookup.consCall ctag (.succ .zero) .zero)) (.succ rest))) := by
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stepTag hstep
 obtain ⟨atag,ha⟩ := LiteralSyntaxValidator.QuantifierNodesProof.appendInstalled p stepTag hstep
 obtain ⟨hzero⟩ := zeroStep p stepTag etag atag ptag ctag hstep he ha hp hc binder rest
 obtain ⟨hunroll⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.scanConsSuccess p stag itag ltag ptag rtag ctag stepTag hs hi hl hp hr hc
  hstep
  (HistoryLookup.consCall ctag (termTask ptag binder) rest) rest (.succ .zero) .zero
 obtain ⟨hbind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag ltag ptag rtag hs hi hl hp hr rest .zero
 obtain ⟨hnil⟩ := LiteralSyntaxScan.StateRecursionProof.nil p itag ltag ptag rtag hi hl hp hr (.succ rest)
 exact ⟨Logic.trans _ _ _ (.mp hunroll hzero) (Logic.trans _ _ _ hbind hnil)⟩

theorem scanSucc {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryLookup.consCall ctag (.succ (.succ .zero)) raw))
   (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest) raw))) := by
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stepTag hstep
 obtain ⟨atag,ha⟩ := LiteralSyntaxValidator.QuantifierNodesProof.appendInstalled p stepTag hstep
 obtain ⟨hsucc⟩ := succStep p stepTag etag atag ptag ctag hstep he ha hp hc binder rest
 obtain ⟨hunroll⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.scanConsSuccess p stag itag ltag ptag rtag ctag stepTag hs hi hl hp hr hc hstep
  (HistoryLookup.consCall ctag (termTask ptag binder) rest) (HistoryLookup.consCall ctag (termTask ptag binder) rest) (.succ (.succ .zero)) raw
 exact ⟨.mp hunroll hsucc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.TermScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.TermScanProof
