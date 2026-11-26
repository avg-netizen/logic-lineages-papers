module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.FieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.WitnessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowFormulaSubstitution GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

theorem witnessValid {n ctx : Nat} (p : Program n) (ltag ftag ptag leftTag rightTag : Nat)
 (hline : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩)
 (hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩) (context raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (topWitness ltag leftTag rightTag context raw)
     (.equal (LiteralSyntaxValidator.formulaCall ftag context raw) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := lineFields ltag leftTag rightTag (.var (0 : Fin (ctx+1))) (liftTerm context) (liftTerm raw)
 let Q := Formula.equal (LiteralSyntaxValidator.formulaCall ftag context raw) (.succ .zero)
 obtain ⟨h⟩ := FieldsProof.fieldsValid p ltag ftag ptag leftTag rightTag hline hf hp hl hr
   (.var (0 : Fin (ctx+1))) (liftTerm context) (liftTerm raw)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
   simpa only [H,Q,GorbowPACore.weaken,substituteFormula,LiteralSyntaxValidator.formulaCall,
     Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,renameTerm] using h
 obtain ⟨he⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 exact ⟨he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.WitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.WitnessProof
