module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open TwoSol20261113.ReflexivityRecognizer
theorem rawAcceptanceImp {n ctx : Nat} (p : Program n) (old : Program 1)
 (ltag ptag ctag atag vtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (raw rawB rawV : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.imp (RawReflexivityDispatcher.valid vtag rawB)
    (.imp (RawReflexivityDispatcher.valid vtag rawV)
     (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineValue ptag ctag atag raw rawB rawV)) (.succ .zero)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let W := RawReflexivityDispatcher.valid vtag rawB
 let U := RawReflexivityDispatcher.valid vtag rawV
 let G := [U,W,V]
 let eq := formulaValue ctag atag raw rawB rawV
 let templ := templateValue ctag rawV
 let lastArg := HistoryLookup.consCall ctag rawB .zero
 let twoArgs := HistoryLookup.consCall ctag raw lastArg
 let threeArgs := HistoryLookup.consCall ctag templ twoArgs
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let pairArgs := HistoryKernel.pairCall ptag threeArgs refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 12) pairArgs
 let rule := HistoryKernel.pairCall ptag .zero payload
 let conclusion := HistoryKernel.pairCall ptag eq rule
 let outLine := lineValue ptag ctag atag raw rawB rawV
 let args := outLine ::ᵥ nil
 have hline : Computes p G (.projection 0) args (HistoryKernel.pairCall ptag .zero conclusion) := projection p G args 0
 have hconclusion := RawReflexivity.LogicalProof.decoded p G ptag hp args (.projection 0) true .zero conclusion hline
 have hrule := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (.projection 0)) true eq rule hconclusion
 have hpayload := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (.projection 0))) true .zero payload hrule
 have hpairArgs := RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (.projection 0)))) true (Term.numeral 12) pairArgs hpayload
 have hthree : Computes p G argsCode args threeArgs :=
  RawReflexivity.LogicalProof.decoded p G ptag hp args (right (right (right (right (.projection 0))))) false threeArgs refs hpairArgs
 have tailOf (a b : Term ctx) : Computes p G HistoryLookup.tail (HistoryLookup.consCall ctag a b ::ᵥ nil) b := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalTailCons n p tag ctag ht hc ctx a b
  exact ⟨.base h⟩
 have headOf (a b : Term ctx) : Computes p G HistoryLookup.head (HistoryLookup.consCall ctag a b ::ᵥ nil) a := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx a b
  exact ⟨.base h⟩
 have htwo := unary p G args HistoryLookup.tail argsCode threeArgs twoArgs hthree (tailOf templ twoArgs)
 have hraw : Computes p G leftTermCode args raw := unary p G args HistoryLookup.head _ twoArgs raw htwo (headOf raw lastArg)
 have hlast := unary p G args HistoryLookup.tail _ twoArgs lastArg htwo (tailOf raw lastArg)
 have hrawB : Computes p G rightTermCode args rawB := unary p G args HistoryLookup.head _ lastArg rawB hlast (headOf rawB .zero)
 have htempl : Computes p G templateCode args templ :=
  unary p G args HistoryLookup.head argsCode threeArgs templ hthree (headOf templ twoArgs)
 let vt1 := HistoryLookup.consCall ctag (.zero : Term ctx) rawV
 let vt2 := HistoryLookup.consCall ctag (.zero : Term ctx) vt1
 have hex1 := unary p G args HistoryLookup.tail templateCode templ vt2 htempl (tailOf .zero vt2)
 have hex2 := unary p G args HistoryLookup.tail _ vt2 vt1 hex1 (tailOf .zero vt1)
 have hrawV : Computes p G fixedTermCode args rawV :=
  unary p G args HistoryLookup.tail _ vt1 rawV hex2 (tailOf .zero rawV)
 have hrebuilt := ConstructorProof.computesLine p G ptag ctag atag hp hc ha args leftTermCode rightTermCode fixedTermCode raw rawB rawV hraw hrawB hrawV
 have hmatch := binary p G args equalCode (.projection 0) (line leftTermCode rightTermCode fixedTermCode)
  outLine outLine (.succ .zero) (projection p G args 0) hrebuilt (equalDiagonal p G outLine)
 have hvalidA : Computes p G termValidator (raw ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (raw ::ᵥ nil)
  have h : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact ⟨localTrans _ _ _ (.base hcopy) h⟩
 have hvalidB : Computes p G termValidator (rawB ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (rawB ::ᵥ nil)
  have h : Hilbert.Local T ctx G W := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨localTrans _ _ _ (.base hcopy) h⟩
 have hvalidV : Computes p G termValidator (rawV ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (rawV ::ᵥ nil)
  have h : Hilbert.Local T ctx G U := .hypothesis List.mem_cons_self
  exact ⟨localTrans _ _ _ (.base hcopy) h⟩
 have hterm := unary p G args termValidator leftTermCode raw (.succ .zero) hraw hvalidA
 have htermB := unary p G args termValidator rightTermCode rawB (.succ .zero) hrawB hvalidB
 have htermV := unary p G args termValidator fixedTermCode rawV (.succ .zero) hrawV hvalidV
 have hinner : Computes p G (conjunction (applyOne termValidator rightTermCode) (applyOne termValidator fixedTermCode)) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) htermB htermV
 have hboth : Computes p G (conjunction (applyOne termValidator leftTermCode)
  (conjunction (applyOne termValidator rightTermCode) (applyOne termValidator fixedTermCode))) args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) hterm hinner
 have hrecognizer : Computes p G recognizer args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) hmatch hboth
 obtain ⟨hout⟩ := choosePositive p G args recognizer old (constant 1 1) .zero (.succ .zero)
  hrecognizer (constantValue p G args 1) ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem internalLogical : Targets.InternalLogical := by
 intro n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw rawB rawV
 obtain ⟨hline⟩ := ConstructorProof.internalLine n p qtag ptag ctag atag hq hp hc ha ctx raw rawB rawV
 obtain ⟨haccept⟩ := rawAcceptanceImp p old ltag ptag ctag atag vtag hl hp hc ha hv raw rawB rawV
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let W := RawReflexivityDispatcher.valid vtag rawB
 let U := RawReflexivityDispatcher.valid vtag rawV
 let G := [U,W,V]
 have hvA : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hvB : Hilbert.Local T ctx G W := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hvV : Hilbert.Local T ctx G U := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base haccept) hvA) hvB) hvV
 have hout := localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace.LogicalProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace.LogicalProof.rawAcceptanceImp
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace.LogicalProof.internalLogical
