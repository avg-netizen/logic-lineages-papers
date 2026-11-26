module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.TestProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open TwoSol20261113.ReflexivityRecognizer
theorem rawAcceptanceImp {n ctx : Nat} (p : Program n)
 (testTag ptag ctag atag vtag : Nat)
 (ht : (nodes p)[testTag]? = some ⟨2,candidateTest⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (raw rawB rawV : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.imp (RawReflexivityDispatcher.valid vtag rawB)
    (.imp (RawReflexivityDispatcher.valid vtag rawV)
     (.equal (RawSuffixSearch.testCall testTag rawV (lineValue ptag ctag atag raw rawB rawV)) (.succ .zero)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let W := RawReflexivityDispatcher.valid vtag rawB
 let U := RawReflexivityDispatcher.valid vtag rawV
 let G := [U,W,V]
 let eq := formulaValue ctag atag raw rawB rawV
 let templ := templateValue ctag atag raw rawV
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
 let testArgs := rawV ::ᵥ outLine ::ᵥ nil
 let aP := applyOne leftTermCode (.projection (1 : Fin 2))
 let bP := applyOne rightTermCode (.projection (1 : Fin 2))
 have hA : Computes p G aP testArgs raw := unary p G testArgs leftTermCode (.projection 1) outLine raw (projection p G testArgs 1) hraw
 have hB : Computes p G bP testArgs rawB := unary p G testArgs rightTermCode (.projection 1) outLine rawB (projection p G testArgs 1) hrawB
 have hV : Computes p G (.projection (0 : Fin 2)) testArgs rawV := projection p G testArgs 0
 have hrebuilt := ConstructorProof.computesLine p G ptag ctag atag hp hc ha testArgs aP bP (.projection 0) raw rawB rawV hA hB hV
 have hmatch := binary p G testArgs equalCode (.projection 1) (line aP bP (.projection 0))
  outLine outLine (.succ .zero) (projection p G testArgs 1) hrebuilt (equalDiagonal p G outLine)
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
 have hterm := unary p G testArgs termValidator aP raw (.succ .zero) hA hvalidA
 have htermB := unary p G testArgs termValidator bP rawB (.succ .zero) hB hvalidB
 have htermV := unary p G testArgs termValidator (.projection 0) rawV (.succ .zero) hV hvalidV
 have hinner : Computes p G (conjunction (applyOne termValidator bP) (applyOne termValidator (.projection 0))) testArgs (.succ .zero) :=
  choosePositive p G testArgs _ _ _ .zero (.succ .zero) htermB htermV
 have hboth : Computes p G (conjunction (applyOne termValidator aP)
  (conjunction (applyOne termValidator bP) (applyOne termValidator (.projection 0)))) testArgs (.succ .zero) :=
  choosePositive p G testArgs _ _ _ .zero (.succ .zero) hterm hinner
 have hrecognizer : Computes p G candidateTest testArgs (.succ .zero) :=
  choosePositive p G testArgs _ _ _ .zero (.succ .zero) hmatch hboth
 obtain ⟨hout⟩ := hrecognizer testTag ht
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem internalTest : Targets.InternalTest := by
 intro n p qtag testTag ptag ctag atag vtag hq ht hp hc ha hv ctx raw rawB rawV
 obtain ⟨hline⟩ := ConstructorProof.internalLine n p qtag ptag ctag atag hq hp hc ha ctx raw rawB rawV
 obtain ⟨haccept⟩ := rawAcceptanceImp p testTag ptag ctag atag vtag ht hp hc ha hv raw rawB rawV
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let W := RawReflexivityDispatcher.valid vtag rawB
 let U := RawReflexivityDispatcher.valid vtag rawV
 let G := [U,W,V]
 have hvA : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hvB : Hilbert.Local T ctx G W := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hvV : Hilbert.Local T ctx G U := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base haccept) hvA) hvB) hvV
 have hleaf := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) testTag rawV _ rawV _ (.base (.logical (.reflexive rawV))) (.base hline)
 have hout := localTrans _ _ _ hleaf hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.TestProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.TestProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.TestProof.rawAcceptanceImp
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.TestProof.internalTest
