module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.SearchProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem substCall {m k arity : Nat} (tag : Nat) (args : List.Vector (Term m) arity)
 (sigma : Fin m → Term k) : substitute sigma (call tag args) =
 call tag (args.map (substitute sigma)) :=
 GorbowPRCallCongruence.Proof.callSubstitution m k arity tag args sigma

theorem boundedWitness {n ctx : Nat} (p : Program n) (old : Program 1) (I : Installation p old)
 (v line : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (HistoryBounds.weakBound v line)
  (.imp (.equal (RawNumericSearch.testCall I.testTag v line) (.succ .zero))
   (.equal (RawNumericSearch.searchCall I.searchTag (.succ line) line) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.upperBody line v
 let P := Formula.equal (RawNumericSearch.testCall I.testTag (liftTerm v) (liftTerm line)) (.succ .zero)
 let G := [P,H]
 have hp : Hilbert.Local T (ctx+1) G P := .hypothesis List.mem_cons_self
 have hh : Hilbert.Local T (ctx+1) G (.equal (liftTerm line) (.add (liftTerm v) (.var 0))) :=
  .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 obtain ⟨hw⟩ := RawNumericSearch.WitnessProof.internalWitness n p RawAddLeftReplace.candidateTest I.toSearch (ctx+1) (liftTerm v) (.var 0) (liftTerm line)
 have hresult := Hilbert.Local.mp (.base hw) hp
 have hs : Hilbert.Local T (ctx+1) G (.equal (.succ (liftTerm line)) (.succ (.add (liftTerm v) (.var 0)))) :=
  localUnary (.succ (.var 0)) _ _ hh
 have hc := callCongruence (T := T) (G := G) I.searchTag
  (.succ (liftTerm line) ::ᵥ liftTerm line ::ᵥ nil)
  (.succ (.add (liftTerm v) (.var 0)) ::ᵥ liftTerm line ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hs
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive _))
     | succ i => exact Fin.elim0 i)
 have hout := localTrans _ _ _ hc hresult
 have hbody : Derivation T (.imp H (GorbowPACore.weaken
  (.imp (.equal (RawNumericSearch.testCall I.testTag v line) (.succ .zero))
   (.equal (RawNumericSearch.searchCall I.searchTag (.succ line) line) (.succ .zero))))) := by
  simpa only [P,GorbowPACore.weaken,substituteFormula,RawNumericSearch.testCall,
   RawNumericSearch.searchCall,liftTerm,renameTerm,substCall,
   List.Vector.map_cons,List.Vector.map_nil,substitute] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
 exact HBQuantifier.existentialElimination T H _ ⟨hbody⟩

theorem internalSearch : Targets.InternalSearch := by
 intro n p old I ctx t u v
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let U := RawReflexivityDispatcher.valid I.validatorTag v
 let G := [U,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hu : Hilbert.Local T ctx G W := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hv : Hilbert.Local T ctx G U := .hypothesis List.mem_cons_self
 obtain ⟨hline⟩ := RawAddLeftReplace.ConstructorProof.internalLine n p I.qtag I.pairTag I.consTag I.appendTag I.hq I.hp I.hc I.ha ctx t u v
 obtain ⟨hb⟩ := RawAddLeftReplace.BoundProof.internalCandidateBound n p I.pairTag I.consTag I.appendTag I.lengthTag I.dropTag I.hp I.hc I.ha I.hlength I.hdrop ctx t u v
 have hbound := Derivation.mp (Derivation.mp (HistoryBounds.PairProof.weakTransport v _ _) hline) hb
 obtain ⟨hcheck⟩ := RawAddLeftReplace.TestProof.internalTest n p I.qtag I.testTag I.pairTag I.consTag I.appendTag I.validatorTag I.hq I.ht I.hp I.hc I.ha I.hv ctx t u v
 obtain ⟨hcover⟩ := boundedWitness p old I v (RawAddLeftReplace.lineCall I.qtag t u v)
 have hout : Hilbert.Local T ctx G _ := .mp (.mp (.base hcover) (.base hbound)) (.mp (.mp (.mp (.base hcheck) ht) hu) hv)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.SearchProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.SearchProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.SearchProof.boundedWitness
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.SearchProof.internalSearch

#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance.SearchProof.substCall
