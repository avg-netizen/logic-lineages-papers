module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.InvariantProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def contents {ctx : Nat} (vtag qctag ctag atag : Nat) (index fuel t u cert : Term ctx) : Formula ctx :=
 .conj (RawReflexivityDispatcher.valid vtag t)
  (.conj (RawReflexivityDispatcher.valid vtag u)
   (.equal (LiteralCheckerAcceptance.coreCall qctag index fuel .zero
    (.add (RawSuccCongruence.inputRaw ctag atag t u) (RawSuccCongruence.inputRaw ctag atag t u)) cert) (.succ .zero)))
theorem substContents {m n : Nat} (sub : Fin m → Term n) v q c a (index fuel t u cert : Term m) :
 substituteFormula sub (contents v q c a index fuel t u cert) =
 contents v q c a (substitute sub index) (substitute sub fuel) (substitute sub t) (substitute sub u) (substitute sub cert) := by
 simp only [contents,RawReflexivityDispatcher.valid,TwoSol20261113.ReflexivityRecognizer.leafCall,
  RawSuccCongruence.inputRaw,RawSuccReplace.binaryValue,HistoryLookup.consCall,HistoryAppend.appendCall,
  LiteralCheckerAcceptance.coreCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substituteFormula,substitute,
  Term.numeral]
theorem substInvariant {m n : Nat} (sub : Fin m → Term n) v q c a l r (index fuel s : Term m) :
 substituteFormula sub (invariant v q c a l r index fuel s) =
 invariant v q c a l r (substitute sub index) (substitute sub fuel) (substitute sub s) := by
 change substituteFormula sub (contents v q c a index fuel (first l s) (second l r s) (third r s)) = _
 simp only [substContents,first,second,third,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
 rfl
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} v q c a l r (index fuel s t : Term ctx) :
 Derivation T (.imp (.equal s t) (.imp (invariant v q c a l r index fuel s) (invariant v q c a l r index fuel t))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (invariant v q c a l r (liftTerm index) (liftTerm fuel) (.var 0)) s t)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substInvariant,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def moveFirst {T : Sentence → Prop} {ctx : Nat} v q c a (index fuel t u cert z : Term ctx) :
 Derivation T (.imp (.equal t z)
  (.imp (contents v q c a index fuel t u cert) (contents v q c a index fuel z u cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents v q c a (liftTerm index) (liftTerm fuel) (.var 0) (liftTerm u) (liftTerm cert)) t z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def moveSecond {T : Sentence → Prop} {ctx : Nat} v q c a (index fuel t u cert z : Term ctx) :
 Derivation T (.imp (.equal u z)
  (.imp (contents v q c a index fuel t u cert) (contents v q c a index fuel t z cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents v q c a (liftTerm index) (liftTerm fuel) (liftTerm t) (.var 0) (liftTerm cert)) u z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def moveThird {T : Sentence → Prop} {ctx : Nat} v q c a (index fuel t u cert z : Term ctx) :
 Derivation T (.imp (.equal cert z)
  (.imp (contents v q c a index fuel t u cert) (contents v q c a index fuel t u z))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (contents v q c a (liftTerm index) (liftTerm fuel) (liftTerm t) (liftTerm u) (.var 0)) cert z)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substContents,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
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
 obtain ⟨hi⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction n p I.ptag I.leftTag I.rightTag I.hp I.hleft I.hright ctx (call I.rightTag (s ::ᵥ nil))
 have hc := HistoryAppend.PositiveProof.binaryCongruence I.ptag (first I.leftTag s) (first I.leftTag s) _ _
  (.logical (.reflexive _)) hi
 exact ⟨Logic.trans _ _ _ hc ho⟩

theorem internalPreservation {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (s index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (invariant I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag index fuel s)
   (invariant I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag index fuel (stepCall I.stepTag s)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := invariant I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag index fuel s
 let t := first I.leftTag s
 let u := second I.leftTag I.rightTag s
 let cert := third I.rightTag s
 let st := RawSuccReplace.succValue I.ctag t
 let su := RawSuccReplace.succValue I.ctag u
 let out := RawSuccCongruence.certificate I.mpTag I.replaceTag I.qtag I.ctag I.atag t u cert
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have ht := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 have hu := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
 have hcert := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrest
 obtain ⟨hvt⟩ := RawSuccCongruence.StatementChecks.exactSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx t
 obtain ⟨hvu⟩ := RawSuccCongruence.StatementChecks.exactSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx u
 have hst := Hilbert.Local.mp (.base hvt) ht
 have hsu := Hilbert.Local.mp (.base hvu) hu
 obtain ⟨hmp⟩ := RawSuccCongruence.StatementChecks.exactCoreCongruence n p old a x I.toCongruence ctx t u cert index fuel
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hmp) ht) hu) hcert
 have hcontents : Hilbert.Local T ctx [H] (contents I.vtag I.qctag I.ctag I.atag index fuel st su out) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hst) (.mp (.mp (.base (.logical (.andIntro _ _))) hsu) hout)
 obtain ⟨⟨hd1⟩,⟨hd2⟩,⟨hd3⟩⟩ := decodeState p old a x I st su out
 let next := state I.ptag st su out
 have h1 := Hilbert.Local.mp (.mp (.base (moveFirst I.vtag I.qctag I.ctag I.atag index fuel st su out (first I.leftTag next)))
  (.base (Support.equalitySymmetry _ _ hd1))) hcontents
 have h2 := Hilbert.Local.mp (.mp (.base (moveSecond I.vtag I.qctag I.ctag I.atag index fuel (first I.leftTag next) su out (second I.leftTag I.rightTag next)))
  (.base (Support.equalitySymmetry _ _ hd2))) h1
 have h3 : Hilbert.Local T ctx [H] (invariant I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag index fuel next) :=
  .mp (.mp (.base (moveThird I.vtag I.qctag I.ctag I.atag index fuel (first I.leftTag next) (second I.leftTag I.rightTag next) out (third I.rightTag next)))
   (.base (Support.equalitySymmetry _ _ hd3))) h2
 obtain ⟨hreconstruct⟩ := reconstructState p old a x I s
 obtain ⟨hstep⟩ := StepProof.internalStep n p old a x I ctx t u cert
 have heq : Derivation T (.equal next (stepCall I.stepTag s)) :=
  Logic.trans _ _ _ (Support.equalitySymmetry _ _ hstep)
   (HistoryLookup.DestructorProof.unaryCallCongruence I.stepTag _ _ hreconstruct)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (transport I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag index fuel next (stepCall I.stepTag s))) (.base heq)) h3))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.InvariantProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.InvariantProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.InvariantProof.internalPreservation
