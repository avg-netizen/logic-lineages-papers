module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ArithmeticProof
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
 (raw rawB : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (leafCall vtag raw) (.succ .zero))
   (.imp (.equal (leafCall vtag rawB) (.succ .zero))
   (.equal (leafCall ltag (RawAddSucc.lineValue ptag ctag atag raw rawB)) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := Formula.equal (leafCall vtag raw) (.succ .zero)
 let W := Formula.equal (leafCall vtag rawB) (.succ .zero)
 let G := [W,V]
 let sr := HistoryLookup.consCall ctag (Term.numeral 2) rawB
 let ar := HistoryLookup.consCall ctag (Term.numeral 3) (HistoryAppend.appendCall atag raw sr)
 let ab := HistoryLookup.consCall ctag (Term.numeral 3) (HistoryAppend.appendCall atag raw rawB)
 let sab := HistoryLookup.consCall ctag (Term.numeral 2) ab
 let eq := RawAddSucc.equalityValue ctag atag raw rawB
 let outLine := RawAddSucc.lineValue ptag ctag atag raw rawB
 let args := outLine ::ᵥ nil
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let lastArg := HistoryLookup.consCall ctag rawB .zero
 let single := HistoryLookup.consCall ctag raw lastArg
 let pairArgs := HistoryKernel.pairCall ptag single refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 3) pairArgs
 let rule := HistoryKernel.pairCall ptag (.succ .zero) payload
 let conclusion := HistoryKernel.pairCall ptag eq rule
 have hline : Computes p G (.projection 0) args (HistoryKernel.pairCall ptag .zero conclusion) :=
  projection p G args 0
 have hconclusion := RawReflexivity.LogicalProof.decoded p G ptag hp args (.projection 0) true .zero conclusion hline
 have hrule := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (.projection 0)) true eq rule hconclusion
 have hpayload := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (.projection 0))) true (.succ .zero) payload hrule
 have hpairArgs := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (.projection 0)))) true
  (Term.numeral 3) pairArgs hpayload
 have hsingle : Computes p G argsCode args single :=
  RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (right (.projection 0))))) false single refs hpairArgs
 have hhead : Computes p G HistoryLookup.head (single ::ᵥ nil) raw := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx raw lastArg
  exact ⟨.base h⟩
 have hraw : Computes p G termCode args raw := unary p G args HistoryLookup.head argsCode _ _ hsingle hhead
 have htail : Computes p G HistoryLookup.tail (single ::ᵥ nil) lastArg := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalTailCons n p tag ctag ht hc ctx raw lastArg
  exact ⟨.base h⟩
 have htailArgs := unary p G args HistoryLookup.tail argsCode single lastArg hsingle htail
 have hheadB : Computes p G HistoryLookup.head (lastArg ::ᵥ nil) rawB := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx rawB .zero
  exact ⟨.base h⟩
 have hrawB : Computes p G secondTermCode args rawB :=
  unary p G args HistoryLookup.head _ lastArg rawB htailArgs hheadB
 have hz := constantValue p G args 0
 have hone := constantValue p G args 1
 have htwo := constantValue p G args 2
 have hthree := constantValue p G args 3
 have hcopyPair (a b : Term ctx) := copies p G HistoryCodec.pair ptag hp (a ::ᵥ b ::ᵥ nil)
 have hcopyCons (a b : Term ctx) := copies p G HistoryCodec.cons ctag hc (a ::ᵥ b ::ᵥ nil)
 have hsr : Computes p G (successorRaw secondTermCode) args sr :=
  binary p G args HistoryCodec.cons _ _ _ _ sr htwo hrawB (hcopyCons _ _)
 have harg := binary p G args HistoryAppend.append termCode (successorRaw secondTermCode) raw sr _ hraw hsr
  (copies p G HistoryAppend.append atag ha (raw ::ᵥ sr ::ᵥ nil))
 have hadd : Computes p G (additionRaw termCode (successorRaw secondTermCode)) args ar :=
  binary p G args HistoryCodec.cons _ _ _ _ ar hthree harg (hcopyCons _ _)
 have habArgs := binary p G args HistoryAppend.append termCode secondTermCode raw rawB _ hraw hrawB
  (copies p G HistoryAppend.append atag ha (raw ::ᵥ rawB ::ᵥ nil))
 have hab : Computes p G (additionRaw termCode secondTermCode) args ab :=
  binary p G args HistoryCodec.cons _ _ _ _ ab hthree habArgs (hcopyCons _ _)
 have hsab : Computes p G (successorRaw (additionRaw termCode secondTermCode)) args sab :=
  binary p G args HistoryCodec.cons _ _ _ _ sab htwo hab (hcopyCons _ _)
 have hdup := binary p G args HistoryAppend.append _ _ ar sab _ hadd hsab
  (copies p G HistoryAppend.append atag ha (ar ::ᵥ sab ::ᵥ nil))
 have heq : Computes p G (equalityRaw termCode secondTermCode) args eq :=
  binary p G args HistoryCodec.cons (constant 1 0) _ .zero _ eq hz hdup (hcopyCons _ _)
 have hlast := binary p G args HistoryCodec.cons secondTermCode (constant 1 0) rawB .zero lastArg hrawB hz (hcopyCons _ _)
 have hsingle' := binary p G args HistoryCodec.cons termCode _ raw lastArg single hraw hlast (hcopyCons _ _)
 have hrefs := binary p G args HistoryCodec.pair (constant 1 0) (constant 1 0) .zero .zero refs hz hz (hcopyPair _ _)
 have hpa := binary p G args HistoryCodec.pair _ _ single refs pairArgs hsingle' hrefs (hcopyPair _ _)
 have hpay := binary p G args HistoryCodec.pair _ _ (Term.numeral 3) pairArgs payload hthree hpa (hcopyPair _ _)
 have hr := binary p G args HistoryCodec.pair _ _ (.succ .zero) payload rule hone hpay (hcopyPair _ _)
 have hco := binary p G args HistoryCodec.pair _ _ eq rule conclusion heq hr (hcopyPair _ _)
 have hrebuilt : Computes p G (RawAddSucc.line termCode secondTermCode) args outLine :=
  binary p G args HistoryCodec.pair _ _ .zero conclusion outLine hz hco (hcopyPair _ _)
 have hmatch := binary p G args equalCode (.projection 0) (RawAddSucc.line termCode secondTermCode)
  outLine outLine (.succ .zero) (projection p G args 0) hrebuilt (equalDiagonal p G outLine)
 have hvalid' : Computes p G termValidator (raw ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (raw ::ᵥ nil)
  have h : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨HistoryCodec.ArithmeticSupport.localTrans _ _ _ (.base hcopy) h⟩
 have hterm := unary p G args termValidator termCode raw (.succ .zero) hraw hvalid'
 have hvalidB : Computes p G termValidator (rawB ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (rawB ::ᵥ nil)
  have h : Hilbert.Local T ctx G W := .hypothesis List.mem_cons_self
  exact ⟨HistoryCodec.ArithmeticSupport.localTrans _ _ _ (.base hcopy) h⟩
 have htermB := unary p G args termValidator secondTermCode rawB (.succ .zero) hrawB hvalidB
 have hboth : Computes p G (conjunction (applyOne termValidator termCode) (applyOne termValidator secondTermCode)) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) hterm htermB
 have hrecognizer : Computes p G recognizer args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) hmatch hboth
 obtain ⟨hout⟩ := choosePositive p G args recognizer old (constant 1 1) .zero (.succ .zero)
  hrecognizer hone ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

theorem internalArithmetic : Targets.InternalArithmetic := by
 intro n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw rawB
 obtain ⟨hline⟩ := ConstructorProof.internalLine n p qtag ptag ctag atag hq hp hc ha ctx raw rawB
 obtain ⟨haccept⟩ := rawAcceptanceImp p old ltag ptag ctag atag vtag hl hp hc ha hv raw rawB
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let W := RawReflexivityDispatcher.valid vtag rawB
 let G := [W,V]
 have hvA : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hvB : Hilbert.Local T ctx G W := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (Hilbert.Local.mp (.base haccept) hvA) hvB
 have hout := HistoryCodec.ArithmeticSupport.localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ArithmeticProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ArithmeticProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ArithmeticProof.rawAcceptanceImp
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.ArithmeticProof.internalArithmetic
