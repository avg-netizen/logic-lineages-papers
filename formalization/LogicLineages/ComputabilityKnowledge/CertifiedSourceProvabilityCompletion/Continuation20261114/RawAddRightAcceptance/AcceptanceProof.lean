module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.DecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.AcceptanceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open RawAddRightReplace

theorem rawAcceptance {n ctx : Nat} (p : Program n) (old : Program 1) (I : Installation p old)
 (t u v : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.logicalTag
      (lineValue I.pairTag I.consTag I.appendTag t u v)) (.succ .zero)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let U := RawReflexivityDispatcher.valid I.validatorTag v
 let G := [U,W,V]
 let outLine := lineValue I.pairTag I.consTag I.appendTag t u v
 let templ := templateValue I.consTag I.appendTag t v
 let pref := prefixValue I.consTag I.appendTag t v
 let stream := HistoryAppend.appendCall I.appendTag pref v
 let len := HistoryLengthOffset.lengthCall I.lengthTag templ
 let args := outLine ::ᵥ nil
 have hvA : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hvB : Hilbert.Local T ctx G W := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hvV : Hilbert.Local T ctx G U := .hypothesis List.mem_cons_self
 obtain ⟨htest⟩ := RawAddRightReplace.TestProof.rawAcceptanceImp p I.testTag I.pairTag I.consTag I.appendTag I.validatorTag I.ht I.hp I.hc I.ha I.hv t u v
 have htestOne := Hilbert.Local.mp (.mp (.mp (.base htest) hvA) hvB) hvV
 obtain ⟨hcover⟩ := RawSuffixOccurrence.Proof.internalCoverage n p candidateTest I.toOccurrence ctx pref v outLine
 have hcovered := Hilbert.Local.mp (.base hcover) htestOne
 obtain ⟨hsplit⟩ := SplitProof.internalSplit n p old I ctx t v
 have hlen := HistoryLookup.DestructorProof.unaryCallCongruence I.lengthTag _ _ hsplit
 have hcount : Hilbert.Local T ctx G (.equal (.succ len)
  (.succ (HistoryLengthOffset.lengthCall I.lengthTag stream))) :=
  localUnary (.succ (.var 0)) _ _ (.base hlen)
 have hcg := callCongruence (T := T) (G := G) I.searchTag
  (.succ len ::ᵥ templ ::ᵥ outLine ::ᵥ nil)
  (.succ (HistoryLengthOffset.lengthCall I.lengthTag stream) ::ᵥ stream ::ᵥ outLine ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hcount
   | succ i => cases i using Fin.cases with
     | zero => exact .base hsplit
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive outLine))
       | succ i => exact Fin.elim0 i)
 have hsearchOne := localTrans _ _ _ hcg hcovered
 have hsearch : Computes p G (RawSuffixSearch.search candidateTest)
  (.succ len ::ᵥ templ ::ᵥ outLine ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨h⟩ := copies p G (RawSuffixSearch.search candidateTest) I.searchTag I.hs (.succ len ::ᵥ templ ::ᵥ outLine ::ᵥ nil) tag ht
  exact ⟨localTrans _ _ _ h hsearchOne⟩
 have htempl := DecoderProof.templateCompute p old I G t u v
 have hlength : Computes p G (applyOne HistoryLengthOffset.lengthProgram templateCode) args len :=
  unary p G args HistoryLengthOffset.lengthProgram templateCode templ len htempl
   (copies p G HistoryLengthOffset.lengthProgram I.lengthTag I.hl (templ ::ᵥ nil))
 have hsucc : Computes p G .succ (len ::ᵥ nil) (.succ len) := by
  intro tag ht
  obtain ⟨h⟩ := Support.intoRegistry p .succ tag ht _ (NamedArithmeticGraph.Equations.successor tag ctx (len ::ᵥ nil))
  exact ⟨.base h⟩
 have hcountCompute : Computes p G (.composition .succ (fun _ => applyOne HistoryLengthOffset.lengthProgram templateCode)) args (.succ len) :=
  unary p G args .succ (applyOne HistoryLengthOffset.lengthProgram templateCode) len (.succ len) hlength hsucc
 have hrecognizer : Computes p G recognizer args (.succ .zero) := by
  apply compose p G (RawSuffixSearch.search candidateTest) searchArguments args
   (.succ len ::ᵥ templ ::ᵥ outLine ::ᵥ nil) (.succ .zero) _ hsearch
  intro i
  cases i using Fin.cases with
  | zero => exact hcountCompute
  | succ i => cases i using Fin.cases with
    | zero => exact htempl
    | succ i => cases i using Fin.cases with
      | zero => exact projection p G args 0
      | succ i => exact Fin.elim0 i
 obtain ⟨hout⟩ := choosePositive p G args recognizer old (constant 1 1) .zero (.succ .zero)
  hrecognizer (constantValue p G args 1) I.logicalTag I.hlogical
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem internalLogical : Targets.InternalLogical := by
 intro n p old I ctx t u v
 obtain ⟨hline⟩ := RawAddRightReplace.ConstructorProof.internalLine n p I.qtag I.pairTag I.consTag I.appendTag I.hq I.hp I.hc I.ha ctx t u v
 obtain ⟨haccept⟩ := rawAcceptance p old I t u v
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence I.logicalTag _ _ hline
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let U := RawReflexivityDispatcher.valid I.validatorTag v
 let G := [U,W,V]
 have hvA : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hvB : Hilbert.Local T ctx G W := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hvV : Hilbert.Local T ctx G U := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (.mp (.mp (.base haccept) hvA) hvB) hvV
 have hout := localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.AcceptanceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.AcceptanceProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.AcceptanceProof.rawAcceptance
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.AcceptanceProof.internalLogical
