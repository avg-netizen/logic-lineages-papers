module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.EquationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.InvariantSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open GorbowSubstitution GorbowFormulaSubstitution RawIteratedSucc

def contents {ctx : Nat} (v q c a : Nat) (index fuel t u w cert : Term ctx) : Formula ctx :=
 .conj (RawReflexivityDispatcher.valid v w)
  (RawEqualityComposition.accepted q c a index fuel (RawAdditionComputation.addRaw c a t u) w cert)
def property {ctx : Nat} (v q c a l r num pref : Nat) (count t index fuel s : Term ctx) : Formula ctx :=
 .conj (.equal (first l s) (LiteralNumeralPrefix.numeralCall num count))
  (.conj (.equal (second l r s) (binaryCall pref count t))
   (contents v q c a index fuel t (LiteralNumeralPrefix.numeralCall num count) (binaryCall pref count t) (third r s)))
theorem substContents {m n : Nat} (sub : Fin m → Term n) v q c a (index fuel t u w cert : Term m) :
 substituteFormula sub (contents v q c a index fuel t u w cert) =
 contents v q c a (substitute sub index) (substitute sub fuel) (substitute sub t) (substitute sub u) (substitute sub w) (substitute sub cert) := by
 simp only [contents,RawReflexivityDispatcher.valid,TwoSol20261113.ReflexivityRecognizer.leafCall,
  RawEqualityComposition.accepted,RawEqualityComposition.eqRaw,RawSuccReplace.binaryValue,
  RawAdditionComputation.addRaw,HistoryLookup.consCall,HistoryAppend.appendCall,LiteralCheckerAcceptance.coreCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substituteFormula,substitute,Term.numeral]
theorem substProperty {m n : Nat} (sub : Fin m → Term n) v q c a l r num pref (count t index fuel s : Term m) :
 substituteFormula sub (property v q c a l r num pref count t index fuel s) =
 property v q c a l r num pref (substitute sub count) (substitute sub t) (substitute sub index) (substitute sub fuel) (substitute sub s) := by
 simp only [property,substituteFormula,substContents,first,second,third,binaryCall,LiteralNumeralPrefix.numeralCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
noncomputable def moveFirst {T : Sentence → Prop} {ctx : Nat} v q c a (index fuel t u w cert z : Term ctx) :
 Derivation T (.imp (.equal u z) (.imp (contents v q c a index fuel t u w cert) (contents v q c a index fuel t z w cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents v q c a (liftTerm index) (liftTerm fuel) (liftTerm t) (.var 0) (liftTerm w) (liftTerm cert)) u z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def moveSecond {T : Sentence → Prop} {ctx : Nat} v q c a (index fuel t u w cert z : Term ctx) :
 Derivation T (.imp (.equal w z) (.imp (contents v q c a index fuel t u w cert) (contents v q c a index fuel t u z cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents v q c a (liftTerm index) (liftTerm fuel) (liftTerm t) (liftTerm u) (.var 0) (liftTerm cert)) w z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def moveThird {T : Sentence → Prop} {ctx : Nat} v q c a (index fuel t u w cert z : Term ctx) :
 Derivation T (.imp (.equal cert z) (.imp (contents v q c a index fuel t u w cert) (contents v q c a index fuel t u w z))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents v q c a (liftTerm index) (liftTerm fuel) (liftTerm t) (liftTerm u) (liftTerm w) (.var 0)) cert z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} v q c a l r num pref (count t index fuel s z : Term ctx) :
 Derivation T (.imp (.equal s z) (.imp (property v q c a l r num pref count t index fuel s)
  (property v q c a l r num pref count t index fuel z))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (property v q c a l r num pref (liftTerm count) (liftTerm t) (liftTerm index) (liftTerm fuel) (.var 0)) s z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def unaryLocal {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} (tag : Nat) (s t : Term ctx)
 (h : Hilbert.Local T ctx G (.equal s t)) :
 Hilbert.Local T ctx G (.equal (GorbowPRDefiningEquations.call tag (s ::ᵥ nil)) (GorbowPRDefiningEquations.call tag (t ::ᵥ nil))) :=
 callCongruence tag (s ::ᵥ nil) (t ::ᵥ nil) (fun i => Fin.cases h (fun j => Fin.elim0 j) i)
theorem decodeState {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t u cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (first I.leftTag (state I.ptag t u cert)) t)) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (second I.leftTag I.rightTag (state I.ptag t u cert)) u)) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (third I.rightTag (state I.ptag t u cert)) cert)) := by
 obtain ⟨hl⟩ := HistoryLookup.DestructorProof.decoderCrossPair p I.leftTag I.ptag false I.hleft I.hp t (HistoryKernel.pairCall I.ptag u cert)
 obtain ⟨hr⟩ := HistoryLookup.DestructorProof.decoderCrossPair p I.rightTag I.ptag true I.hright I.hp t (HistoryKernel.pairCall I.ptag u cert)
 obtain ⟨hll⟩ := HistoryLookup.DestructorProof.decoderCrossPair p I.leftTag I.ptag false I.hleft I.hp u cert
 obtain ⟨hrr⟩ := HistoryLookup.DestructorProof.decoderCrossPair p I.rightTag I.ptag true I.hright I.hp u cert
 exact ⟨⟨hl⟩,⟨Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ hr) hll⟩,
  ⟨Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ hr) hrr⟩⟩

theorem reconstructState {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (state I.ptag (first I.leftTag s) (second I.leftTag I.rightTag s) (third I.rightTag s)) s)) := by
 obtain ⟨ho⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction n p I.ptag I.leftTag I.rightTag I.hp I.hleft I.hright ctx s
 obtain ⟨hi⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction n p I.ptag I.leftTag I.rightTag I.hp I.hleft I.hright ctx (GorbowPRDefiningEquations.call I.rightTag (s ::ᵥ nil))
 have hc := HistoryAppend.PositiveProof.binaryCongruence I.ptag (first I.leftTag s) (first I.leftTag s) _ _
  (.logical (.reflexive _)) hi
 exact ⟨Logic.trans _ _ _ hc ho⟩


theorem numeralValid {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (RawReflexivityDispatcher.valid I.vtag (LiteralNumeralPrefix.numeralCall I.numeralTag count))) := by
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p I.vtag I.hv
 obtain ⟨hscan⟩ := LiteralNumeralPrefix.StatementChecks.exactScan n p I.numeralTag stag I.ptag I.ctag I.hnumeral hs I.hp I.hc ctx count .zero .zero
 obtain ⟨hv⟩ := RawSuccCongruence.ValidityProof.localBinding p [] I.vtag stag I.ptag I.ctag I.hv hs I.hp I.hc
  (LiteralNumeralPrefix.numeralCall I.numeralTag count) (.base hscan)
 exact ⟨Hilbert.Local.finish hv⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.InvariantSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.InvariantSupport
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.InvariantSupport.decodeState
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.InvariantSupport.reconstructState
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.InvariantSupport.numeralValid
