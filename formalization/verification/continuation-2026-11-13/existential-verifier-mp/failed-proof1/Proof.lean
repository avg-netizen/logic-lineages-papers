module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.LogicProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel LiteralRawMP LiteralMPRun NamedArithmeticGraph LogicProof

theorem internalProvabilityMP : Targets.InternalProvabilityMP := by
 intro l a baseX n p itag ltag atag ptag ctag dtag droptag rtag dispatcherTag hi hl ha hp hc hd hdrop hr hdispatch
 intro mtag qtag vtag hm hq hv ctx index context phi psi
 let T := GorbowPRNumeralCalculation.Theory p
 let rawI := implicationRaw atag ctag phi psi
 let codeI := Term.add rawI rawI
 let codeA := Term.add phi phi
 let codeO := Term.add psi psi
 let Q := provability vtag index context codeO
 let lift4 : Term ctx → Term (ctx+1+1+1+1) := fun t => liftTerm (liftTerm (liftTerm (liftTerm t)))
 let A := GorbowPACore.weaken (GorbowPACore.weaken (body vtag index context codeI))
 let B := body vtag (liftTerm (liftTerm index)) (liftTerm (liftTerm context)) (liftTerm (liftTerm codeA))
 let rawI4 := implicationRaw atag ctag (lift4 phi) (lift4 psi)
 let inputI := success vtag (lift4 index) (.var 3) (lift4 context) (.add rawI4 rawI4) (.var 2)
 let inputA := success vtag (lift4 index) (.var 1) (lift4 context) (.add (lift4 phi) (lift4 phi)) (.var 0)
 let output := success vtag (lift4 index) (.add (.var 3) (.var 1)) (lift4 context)
  (.add (lift4 psi) (lift4 psi)) (certificate mtag (lift4 context) (lift4 psi) (.var 2) (.var 0))
 obtain ⟨hmp⟩ := SaturatedVerifierMP.StatementChecks.internalVerifierMP l a baseX n p itag ltag atag ptag ctag dtag droptag rtag dispatcherTag
  hi hl ha hp hc hd hdrop hr hdispatch mtag qtag vtag hm hq hv (ctx+1+1+1+1)
  (lift4 context) (lift4 phi) (lift4 psi) (.var 2) (.var 0) (lift4 index) (.var 3) (.var 1)
 have hA : Hilbert.Local T (ctx+1+1+1+1) [B,A] A := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hB : Hilbert.Local T (ctx+1+1+1+1) [B,A] B := .hypothesis List.mem_cons_self
 have ai : Hilbert.Local T (ctx+1+1+1+1) [B,A] inputI := by
  simpa only [A,inputI,body,codeI,rawI,rawI4,lift4,GorbowPACore.weaken,substituteFormula,
   success,inputs,implicationRaw,HistoryLookup.consCall,HistoryAppend.appendCall,HistoryKernel.pairCall,Logic.substCall,
   liftTerm,renameTerm,Term.numeral,substitute,List.Vector.map_cons,List.Vector.map_nil] using hA
 have aa : Hilbert.Local T (ctx+1+1+1+1) [B,A] inputA := by
  simpa only [B,inputA,body,codeA,lift4,liftTerm,renameTerm,substitute] using hB
 have pair : Hilbert.Local T (ctx+1+1+1+1) [B,A] (.conj inputI inputA) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) ai) aa
 have out : Hilbert.Local T (ctx+1+1+1+1) [B,A] output := .mp (.base hmp) pair
 have introRule := LogicProof.introduce (T := T) vtag (lift4 index) (lift4 context)
  (.add (lift4 psi) (lift4 psi)) (.add (.var 3) (.var 1))
  (certificate mtag (lift4 context) (lift4 psi) (.var 2) (.var 0))
 have outProv := Hilbert.Local.mp (.base introRule) out
 have derived : Derivation T (.imp A (.imp B
  (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken Q)))))) := by
  simpa only [Q,codeO,lift4,GorbowPACore.weaken,substituteFormula,substProvability,liftTerm,renameTerm,substitute] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge outProv))
 exact twoProvabilities T vtag index context codeI codeA Q derived
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Proof
