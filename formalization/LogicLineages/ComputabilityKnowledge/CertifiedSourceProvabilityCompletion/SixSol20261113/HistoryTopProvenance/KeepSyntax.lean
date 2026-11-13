module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OutputRestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSyntax
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryIteratorSuffix.WitnessProof (substPair)

def keep {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (code context raw tail remaining index fuel : Term ctx) : Formula ctx :=
 let target := HistoryRunSplice.state ptag (.succ (HistoryLookup.consCall ctag
   (HistoryKernel.pairCall ptag context raw) tail)) remaining
 let Q := topWitness vtag leftTag rightTag context raw
 .imp (.imp (.equal code target) Q)
   (.imp (.equal (HistoryKernel.kernelCall (kernelTag itag) code index fuel) target) Q)

def stateKeep {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (option lines context raw tail remaining index fuel : Term ctx) : Formula ctx :=
 keep itag ptag ctag vtag leftTag rightTag (HistoryRunSplice.state ptag option lines)
   context raw tail remaining index fuel

theorem substKeep {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag
 (code context raw tail remaining index fuel : Term m) :
 substituteFormula sub (keep itag ptag ctag vtag leftTag rightTag code context raw tail remaining index fuel) =
 keep itag ptag ctag vtag leftTag rightTag (substitute sub code) (substitute sub context)
   (substitute sub raw) (substitute sub tail) (substitute sub remaining) (substitute sub index) (substitute sub fuel) := by
 simp only [keep,substituteFormula,SyntaxProof.substWitness,HistoryRunSplice.state,
   HistoryKernel.kernelCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
   HistoryLookup.DropEquationsProof.substCons,substPair,substitute]

theorem substStateKeep {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag
 (option lines context raw tail remaining index fuel : Term m) :
 substituteFormula sub (stateKeep itag ptag ctag vtag leftTag rightTag option lines context raw tail remaining index fuel) =
 stateKeep itag ptag ctag vtag leftTag rightTag (substitute sub option) (substitute sub lines)
   (substitute sub context) (substitute sub raw) (substitute sub tail) (substitute sub remaining) (substitute sub index) (substitute sub fuel) := by
 simp only [stateKeep,substKeep,HistoryRunSplice.state,substPair]

theorem keepAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag
 (code context raw tail remaining index fuel : Term ctx) :
 GorbowStandardInstances.instantiate
   (keep itag ptag ctag vtag leftTag rightTag (.var 0) (liftTerm context) (liftTerm raw)
     (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)) code =
 keep itag ptag ctag vtag leftTag rightTag code context raw tail remaining index fuel := by
 simp only [GorbowStandardInstances.instantiate,substKeep,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def transport {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag
 (a b context raw tail remaining index fuel : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp
   (keep itag ptag ctag vtag leftTag rightTag a context raw tail remaining index fuel)
   (keep itag ptag ctag vtag leftTag rightTag b context raw tail remaining index fuel))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
   (keep itag ptag ctag vtag leftTag rightTag (.var 0) (liftTerm context) (liftTerm raw)
     (liftTerm tail) (liftTerm remaining) (liftTerm index) (liftTerm fuel)) a b)
 simpa only [GorbowPACore.logicalFormula,keepAt] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSyntax
