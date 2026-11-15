module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open TwoSol20261113.ReflexivityRecognizer

theorem rawAcceptanceImp (a b : Term 1) {n ctx : Nat} (p : Program n) (old : Program 1)
 (ltag ptag ctag atag vtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf a b old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩) (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid vtag raw)
  (.equal (leafCall ltag (RawEqualityInstantiation.lineValue ptag ctag atag a b raw)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let G := [V]
 let eq := RawEqualityInstantiation.formulaValue ctag atag a b raw
 let templ := Term.numeral (RawEqualityInstantiation.templateCode a b)
 let lastArg := HistoryLookup.consCall ctag raw .zero
 let twoArgs := HistoryLookup.consCall ctag templ lastArg
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let pairArgs := HistoryKernel.pairCall ptag twoArgs refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 13) pairArgs
 let rule := HistoryKernel.pairCall ptag .zero payload
 let conclusion := HistoryKernel.pairCall ptag eq rule
 let outLine := RawEqualityInstantiation.lineValue ptag ctag atag a b raw
 let args := outLine ::ᵥ nil
 have hline : Computes p G (.projection 0) args (HistoryKernel.pairCall ptag .zero conclusion) := projection p G args 0
 have hconclusion := RawReflexivity.LogicalProof.decoded p G ptag hp args (.projection 0) true .zero conclusion hline
 have hrule := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (.projection 0)) true eq rule hconclusion
 have hpayload := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (.projection 0))) true .zero payload hrule
 have hpairArgs := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (.projection 0)))) true (Term.numeral 13) pairArgs hpayload
 have htwo : Computes p G argsCode args twoArgs :=
  RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (right (.projection 0))))) false twoArgs refs hpairArgs
 have htail : Computes p G HistoryLookup.tail (twoArgs ::ᵥ nil) lastArg := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalTailCons n p tag ctag ht hc ctx templ lastArg
  exact ⟨.base h⟩
 have hhead : Computes p G HistoryLookup.head (lastArg ::ᵥ nil) raw := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx raw .zero
  exact ⟨.base h⟩
 have hlast := unary p G args HistoryLookup.tail argsCode twoArgs lastArg htwo htail
 have hraw : Computes p G argumentCode args raw := unary p G args HistoryLookup.head _ lastArg raw hlast hhead
 have hbuild : Computes p G (RawEqualityInstantiation.line a b) (raw ::ᵥ nil) outLine := by
  intro tag ht
  obtain ⟨h⟩ := RawEqualityInstantiation.StatementChecks.exactGraph a b n p tag ptag ctag atag ht hp hc ha ctx raw
  exact ⟨.base h⟩
 have hrebuilt := unary p G args (RawEqualityInstantiation.line a b) argumentCode raw outLine hraw hbuild
 have hmatch := binary p G args equalCode (.projection 0) (applyOne (RawEqualityInstantiation.line a b) argumentCode)
  outLine outLine (.succ .zero) (projection p G args 0) hrebuilt (equalDiagonal p G outLine)
 have hvalid : Computes p G termValidator (raw ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (raw ::ᵥ nil)
  have h : Hilbert.Local T ctx G V := .hypothesis List.mem_cons_self
  exact ⟨localTrans _ _ _ (.base hcopy) h⟩
 have hterm := unary p G args termValidator argumentCode raw (.succ .zero) hraw hvalid
 have hrecognizer : Computes p G (recognizer a b) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) hmatch hterm
 obtain ⟨hout⟩ := choosePositive p G args (recognizer a b) old (constant 1 1) .zero (.succ .zero)
  hrecognizer (constantValue p G args 1) ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

theorem internalLogical : Targets.InternalLogical := by
 intro a b n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw
 obtain ⟨hline⟩ := RawEqualityInstantiation.StatementChecks.exactGraph a b n p qtag ptag ctag atag hq hp hc ha ctx raw
 obtain ⟨haccept⟩ := rawAcceptanceImp a b p old ltag ptag ctag atag vtag hl hp hc ha hv raw
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 have hvA : Hilbert.Local T ctx [V] V := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (.base haccept) hvA
 have hout := localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.LogicalProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.LogicalProof.rawAcceptanceImp
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.LogicalProof.internalLogical
