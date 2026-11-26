module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.TransportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
noncomputable def moveLeft {T : Sentence → Prop} {ctx : Nat} q c a (index fuel t v cert w : Term ctx) :
 Derivation T (.imp (.equal t w)
  (.imp (RawEqualityComposition.accepted q c a index fuel t v cert)
   (RawEqualityComposition.accepted q c a index fuel w v cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (RawEqualityComposition.accepted q c a (liftTerm index) (liftTerm fuel) (.var 0) (liftTerm v) (liftTerm cert)) t w)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,RawEqualityComposition.accepted,
  RawEqualityComposition.eqRaw,RawSuccReplace.binaryValue,HistoryLookup.consCall,HistoryAppend.appendCall,
  LiteralCheckerAcceptance.coreCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  substituteFormula,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,Term.numeral] using h
noncomputable def moveCertificate {T : Sentence → Prop} {ctx : Nat} q c a (index fuel t v cert w : Term ctx) :
 Derivation T (.imp (.equal cert w)
  (.imp (RawEqualityComposition.accepted q c a index fuel t v cert)
   (RawEqualityComposition.accepted q c a index fuel t v w))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (RawEqualityComposition.accepted q c a (liftTerm index) (liftTerm fuel) (liftTerm t) (liftTerm v) (.var 0)) cert w)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,RawEqualityComposition.accepted,
  RawEqualityComposition.eqRaw,RawSuccReplace.binaryValue,HistoryLookup.consCall,HistoryAppend.appendCall,
  LiteralCheckerAcceptance.coreCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  substituteFormula,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,Term.numeral] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.TransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.TransportProof
