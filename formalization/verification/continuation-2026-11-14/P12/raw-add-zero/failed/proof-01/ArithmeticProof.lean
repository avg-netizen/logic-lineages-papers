module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ArithmeticProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityRecognizer
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem rawAcceptanceImp {n ctx : Nat} (p : Program n) (old : Program 1)
 (ltag ptag ctag atag vtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,arithmeticLeaf old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩)
 (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (leafCall vtag raw) (.succ .zero))
   (.equal (leafCall ltag (RawAddZero.lineValue ptag ctag atag raw)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := Formula.equal (leafCall vtag raw) (.succ .zero)
 let G := [V]
 let zr := HistoryLookup.consCall ctag (.succ (.zero : Term ctx)) .zero
 let ar := HistoryLookup.consCall ctag (Term.numeral 3) (HistoryAppend.appendCall atag raw zr)
 let eq := RawAddZero.equalityValue ctag atag raw
 let outLine := RawAddZero.lineValue ptag ctag atag raw
 let args := outLine ::ᵥ nil
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let single := HistoryLookup.consCall ctag raw .zero
 let pairArgs := HistoryKernel.pairCall ptag single refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 2) pairArgs
 let rule := HistoryKernel.pairCall ptag (.succ .zero) payload
 let conclusion := HistoryKernel.pairCall ptag eq rule
 have hline : Computes p G (.projection 0) args (HistoryKernel.pairCall ptag .zero conclusion) :=
  projection p G args 0
 have hconclusion := RawReflexivity.LogicalProof.decoded p G ptag hp args (.projection 0) true .zero conclusion hline
 have hrule := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (.projection 0)) true eq rule hconclusion
 have hpayload := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (.projection 0))) true (.succ .zero) payload hrule
 have hpairArgs := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (.projection 0)))) true
  (Term.numeral 2) pairArgs hpayload
 have hsingle : Computes p G argsCode args single :=
  RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (right (.projection 0))))) false single refs hpairArgs
 have hhead : Computes p G HistoryLookup.head (single ::ᵥ nil) raw := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx raw .zero
  exact ⟨.base h⟩
 have hraw : Computes p G termCode args raw := unary p G args HistoryLookup.head argsCode _ _ hsingle hhead
 have hz := constantValue p G args 0
 have hone := constantValue p G args 1
 have htwo := constantValue p G args 2
 have hthree := constantValue p G args 3
 have hcopyPair (a b : Term ctx) := copies p G HistoryCodec.pair ptag hp (a ::ᵥ b ::ᵥ nil)
 have hcopyCons (a b : Term ctx) := copies p G HistoryCodec.cons ctag hc (a ::ᵥ b ::ᵥ nil)
 have hzeroRaw : Computes p G zeroRaw args zr :=
  binary p G args HistoryCodec.cons (constant 1 1) (constant 1 0) (.succ .zero) .zero zr
   hone hz (hcopyCons _ _)
 have harg := binary p G args HistoryAppend.append termCode zeroRaw raw zr _ hraw hzeroRaw
  (copies p G HistoryAppend.append atag ha (raw ::ᵥ zr ::ᵥ nil))
 have hadd : Computes p G (addZeroRaw termCode) args ar :=
  binary p G args HistoryCodec.cons (constant 1 3) _ (Term.numeral 3) _ ar hthree harg (hcopyCons _ _)
 have hdup := binary p G args HistoryAppend.append (addZeroRaw termCode) termCode ar raw _ hadd hraw
  (copies p G HistoryAppend.append atag ha (ar ::ᵥ raw ::ᵥ nil))
 have heq : Computes p G (equalityRaw termCode) args eq :=
  binary p G args HistoryCodec.cons (constant 1 0) _ .zero _ eq hz hdup (hcopyCons _ _)
 have hsingle' := binary p G args HistoryCodec.cons termCode (constant 1 0) raw .zero single hraw hz (hcopyCons _ _)
 have hrefs := binary p G args HistoryCodec.pair (constant 1 0) (constant 1 0) .zero .zero refs hz hz (hcopyPair _ _)
 have hpa := binary p G args HistoryCodec.pair _ _ single refs pairArgs hsingle' hrefs (hcopyPair _ _)
 have hpay := binary p G args HistoryCodec.pair _ _ (Term.numeral 2) pairArgs payload htwo hpa (hcopyPair _ _)
 have hr := binary p G args HistoryCodec.pair _ _ (.succ .zero) payload rule hone hpay (hcopyPair _ _)
 have hco := binary p G args HistoryCodec.pair _ _ eq rule conclusion heq hr (hcopyPair _ _)
 have hrebuilt : Computes p G (RawAddZero.line termCode) args outLine :=
  binary p G args HistoryCodec.pair _ _ .zero conclusion outLine hz hco (hcopyPair _ _)
 have hmatch := binary p G args equalCode (.projection 0) (RawAddZero.line termCode)
  outLine outLine (.succ .zero) (projection p G args 0) hrebuilt (equalDiagonal p G outLine)
 have hvalid' : Computes p G termValidator (raw ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (raw ::ᵥ nil)
  have h : Hilbert.Local T ctx G V := .hypothesis List.mem_cons_self
  exact ⟨HistoryCodec.ArithmeticSupport.localTrans _ _ _ (.base hcopy) h⟩
 have hterm := unary p G args termValidator termCode raw (.succ .zero) hraw hvalid'
 have hrecognizer : Computes p G recognizer args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) hmatch hterm
 obtain ⟨hout⟩ := choosePositive p G args recognizer old (constant 1 1) .zero (.succ .zero)
  hrecognizer hone ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

theorem internalArithmetic : Targets.InternalArithmetic := by
 intro n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw
 obtain ⟨hline⟩ := ConstructorProof.internalLine n p qtag ptag ctag atag hq hp hc ha ctx raw
 obtain ⟨haccept⟩ := rawAcceptanceImp p old ltag ptag ctag atag vtag hl hp hc ha hv raw
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 exact ⟨Hilbert.compose (Logic.oneTransport _ _ (Support.equalitySymmetry _ _ hleaf)) haccept⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ArithmeticProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ArithmeticProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ArithmeticProof.rawAcceptanceImp
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.ArithmeticProof.internalArithmetic
