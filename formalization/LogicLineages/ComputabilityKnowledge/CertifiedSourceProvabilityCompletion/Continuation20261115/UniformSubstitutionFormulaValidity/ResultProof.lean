module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.RelationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.ResultProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformSubstitutionChunkTransport
/-- Eliminate the actual arbitrary new-stack witness using only its projected
length equation. No native decode or assumed final empty stack. -/
theorem complete {n ctx : Nat} (p : Program n) (stag len q l r ctag : Nat)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (tasks chunk : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (results stag len q l r tasks chunk .zero)
   (.equal (LiteralSyntaxScan.scanCall stag tasks chunk) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := resultBody stag len q l r (liftTerm tasks) (liftTerm chunk) .zero (.var (0 : Fin (ctx+1)))
 let Q := Formula.equal (LiteralSyntaxScan.scanCall stag tasks chunk) (.succ .zero)
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 have hs := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨he⟩ := RelationProof.emptyResult p len q l r ctag hlen hc (.var (0 : Fin (ctx+1)))
 have hz := Hilbert.Local.mp (.base he) hrel
 have hsucc := localUnary (.succ (.var 0)) _ _ hz
 have hsucc' : Hilbert.Local T (ctx+1) [H] (.equal (.succ (.var 0)) (.succ .zero)) := by
  simpa only [GorbowStandardInstances.instantiate,substitute,Fin.cases_zero] using hsucc
 have hout := localTrans _ _ _ hs hsucc'
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,GorbowPACore.weaken,substituteFormula,LiteralSyntaxScan.scanCall,Logic.substCall,
   List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,renameTerm] using hout.discharge.finish
 exact HBQuantifier.existentialElimination T H Q ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.ResultProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.ResultProof
