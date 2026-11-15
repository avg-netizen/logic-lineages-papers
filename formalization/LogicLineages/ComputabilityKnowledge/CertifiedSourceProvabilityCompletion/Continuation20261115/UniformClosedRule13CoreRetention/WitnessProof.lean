module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.IterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.WitnessProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalCoreRetention.WitnessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralCheckerAcceptance LiteralCheckerAcceptance.WitnessProof LiteralCheckerAuxiliaries

theorem witnessRetention {n ctx : Nat} (p : Program n) (v l a : Program 1) (x : Program 3) (ot nt ptag ctag : Nat)
 (ho : (nodes p)[ot]? = some ⟨4,Iteration.original v l a x⟩)
 (hn : (nodes p)[nt]? = some ⟨4,Iteration.extended v l a x⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (index fuel context formula code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (witness ptag ctag (runCall ot ptag index fuel code) context formula)
        (witness ptag ctag (runCall nt ptag index fuel code) context formula))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let O := runCall ot ptag index fuel code
 let N := runCall nt ptag index fuel code
 let Q := witness ptag ctag N context formula
 let H := inner ptag ctag (liftTerm O) (liftTerm context) (liftTerm formula) (.var (0 : Fin (ctx+1)))
 let raw : Term (ctx+2) := .var (Fin.succ (0 : Fin (ctx+1)))
 let tail : Term (ctx+2) := .var 0
 let ix := liftTerm (liftTerm index)
 let fu := liftTerm (liftTerm fuel)
 let co := liftTerm (liftTerm code)
 let requested := liftTerm (liftTerm context)
 let fm := liftTerm (liftTerm formula)
 have hh : Hilbert.Local T (ctx+2) [H]
  (body ptag ctag (runCall ot ptag ix fu co) requested fm raw tail) := by
  simpa only [H,inner,O,ix,fu,co,requested,fm,raw,tail,liftTerm,renameTerm,substRun,substitute] using
   (Hilbert.Local.hypothesis List.mem_cons_self : Hilbert.Local T (ctx+2) [H] H)
 have hformula := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hstate := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨hs⟩ := Iteration.Proof.internalIteratorRetention n p v l a x ot nt ptag ctag ho hn hp hc (ctx+2)
  co (HistoryKernel.pairCall ptag (.succ .zero) co) ix fu
  (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag requested raw) tail) .zero
 have newState := Hilbert.Local.mp (.base hs) hstate
 have newBody : Hilbert.Local T (ctx+2) [H] (body ptag ctag (runCall nt ptag ix fu co) requested fm raw tail) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hformula) newState
 have out := Hilbert.Local.mp (.base (introWitness ptag ctag (runCall nt ptag ix fu co) requested fm raw tail)) newBody
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,N,weakenWitness,ix,fu,co,requested,fm,liftTerm,renameTerm,substRun] using Hilbert.Local.finish (Hilbert.Local.discharge out)
 obtain ⟨hi⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨he⟩ := HBQuantifier.existentialElimination T (outer ptag ctag O context formula) Q ⟨hi⟩
 exact ⟨he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.WitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.WitnessProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.WitnessProof.witnessRetention
