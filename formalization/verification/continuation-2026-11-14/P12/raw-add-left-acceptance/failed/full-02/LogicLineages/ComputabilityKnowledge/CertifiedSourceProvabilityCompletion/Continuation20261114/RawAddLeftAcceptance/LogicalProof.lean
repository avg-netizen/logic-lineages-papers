module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.SearchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem internalLogical : Targets.InternalLogical := by
 intro n p old I ctx t u v
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let U := RawReflexivityDispatcher.valid I.validatorTag v
 let G := [U,W,V]
 let line := RawAddLeftReplace.lineCall I.qtag t u v
 let args := line ::ᵥ nil
 have ht : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hu : Hilbert.Local T ctx G W := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hv : Hilbert.Local T ctx G U := .hypothesis List.mem_cons_self
 obtain ⟨hsearch⟩ := SearchProof.internalSearch n p old I ctx t u v
 have hone := Hilbert.Local.mp (.mp (.mp (.base hsearch) ht) hu) hv
 have hsearchCompute : Computes p G (RawNumericSearch.search RawAddLeftReplace.candidateTest)
  (.succ line ::ᵥ line ::ᵥ nil) (.succ .zero) := by
  intro tag htag
  obtain ⟨hc⟩ := copies p G _ I.searchTag I.hs (.succ line ::ᵥ line ::ᵥ nil) tag htag
  exact ⟨localTrans _ _ _ hc hone⟩
 have hsucc : Computes p G .succ (line ::ᵥ nil) (.succ line) := by
  intro tag htag
  obtain ⟨h⟩ := Support.intoRegistry p .succ tag htag _ (NamedArithmeticGraph.Equations.successor tag ctx (line ::ᵥ nil))
  exact ⟨.base h⟩
 have hcount : Computes p G (.composition .succ (fun _ => .projection 0)) args (.succ line) :=
  unary p G args .succ (.projection 0) line (.succ line) (projection p G args 0) hsucc
 have hrecognizer : Computes p G RawAddLeftReplace.recognizer args (.succ .zero) := by
  apply compose p G (RawNumericSearch.search RawAddLeftReplace.candidateTest)
   RawAddLeftReplace.searchArguments args (.succ line ::ᵥ line ::ᵥ nil) (.succ .zero) _ hsearchCompute
  intro i
  cases i using Fin.cases with
  | zero => exact hcount
  | succ i => cases i using Fin.cases with
    | zero => exact projection p G args 0
    | succ i => exact Fin.elim0 i
 obtain ⟨hout⟩ := choosePositive p G args RawAddLeftReplace.recognizer old (constant 1 1)
  .zero (.succ .zero) hrecognizer (constantValue p G args 1) I.logicalTag I.hlogical
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.LogicalProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.LogicalProof.internalLogical
