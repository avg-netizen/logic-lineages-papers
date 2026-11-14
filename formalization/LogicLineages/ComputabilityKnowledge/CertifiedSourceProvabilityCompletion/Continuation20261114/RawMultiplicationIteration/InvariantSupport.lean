module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.EquationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RawIteratedSucc (first second third state)
open RawAdditionIteration (binaryCall)
def contents {ctx : Nat} (q c a num : Nat) (index fuel m u z cert : Term ctx) : Formula ctx :=
 RawEqualityComposition.accepted q c a index fuel
  (RawMultiplicationComputation.mulRaw c a (LiteralNumeralPrefix.numeralCall num m) u)
  (LiteralNumeralPrefix.numeralCall num z) cert
def property {ctx : Nat} (q c a l r num : Nat) (count m index fuel s : Term ctx) : Formula ctx :=
 .conj (.equal (first l s) (LiteralNumeralPrefix.numeralCall num count))
  (.conj (.equal (second l r s) (.mul m count))
   (contents q c a num index fuel m (LiteralNumeralPrefix.numeralCall num count) (.mul m count) (third r s)))
theorem substContents {m n : Nat} (sub : Fin m → Term n) q c a num (index fuel v u z cert : Term m) :
 substituteFormula sub (contents q c a num index fuel v u z cert) =
 contents q c a num (substitute sub index) (substitute sub fuel) (substitute sub v) (substitute sub u) (substitute sub z) (substitute sub cert) := by
 simp only [contents,RawEqualityComposition.accepted,RawEqualityComposition.eqRaw,RawSuccReplace.binaryValue,
  RawMultiplicationComputation.mulRaw,LiteralNumeralPrefix.numeralCall,HistoryLookup.consCall,HistoryAppend.appendCall,
  LiteralCheckerAcceptance.coreCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substituteFormula,substitute,Term.numeral]
theorem substProperty {m n : Nat} (sub : Fin m → Term n) q c a l r num (count v index fuel s : Term m) :
 substituteFormula sub (property q c a l r num count v index fuel s) =
 property q c a l r num (substitute sub count) (substitute sub v) (substitute sub index) (substitute sub fuel) (substitute sub s) := by
 simp only [property,substituteFormula,substContents,first,second,third,LiteralNumeralPrefix.numeralCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
noncomputable def moveFirst {T : Sentence → Prop} {ctx : Nat} q c a num (index fuel m u z cert w : Term ctx) :
 Derivation T (.imp (.equal u w) (.imp (contents q c a num index fuel m u z cert) (contents q c a num index fuel m w z cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents q c a num (liftTerm index) (liftTerm fuel) (liftTerm m) (.var 0) (liftTerm z) (liftTerm cert)) u w)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def moveSecond {T : Sentence → Prop} {ctx : Nat} q c a num (index fuel m u z cert w : Term ctx) :
 Derivation T (.imp (.equal z w) (.imp (contents q c a num index fuel m u z cert) (contents q c a num index fuel m u w cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents q c a num (liftTerm index) (liftTerm fuel) (liftTerm m) (liftTerm u) (.var 0) (liftTerm cert)) z w)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def moveThird {T : Sentence → Prop} {ctx : Nat} q c a num (index fuel m u z cert w : Term ctx) :
 Derivation T (.imp (.equal cert w) (.imp (contents q c a num index fuel m u z cert) (contents q c a num index fuel m u z w))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents q c a num (liftTerm index) (liftTerm fuel) (liftTerm m) (liftTerm u) (liftTerm z) (.var 0)) cert w)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} q c a l r num (count m index fuel s z : Term ctx) :
 Derivation T (.imp (.equal s z) (.imp (property q c a l r num count m index fuel s) (property q c a l r num count m index fuel z))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (property q c a l r num (liftTerm count) (liftTerm m) (liftTerm index) (liftTerm fuel) (.var 0)) s z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable abbrev unaryLocal := @RawRetainedAdditionIteration.InvariantSupport.unaryLocal
abbrev decodeState := @RawRetainedAdditionIteration.InvariantSupport.decodeState
abbrev reconstructState := @RawRetainedAdditionIteration.InvariantSupport.reconstructState
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantSupport
