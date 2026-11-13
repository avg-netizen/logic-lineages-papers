module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.WitnessProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.ShapeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAuxiliaries WitnessProof
open HistoryCodec.ArithmeticSupport HistoryIteratorSuffix.WitnessProof

def sound {ctx : Nat} (ftag dtag ptag ctag : Nat) (state requested formula certificate : Term ctx) : Formula ctx :=
  .imp (.equal (finalCall ftag state requested formula certificate) (.succ .zero))
    (.imp (.equal (unaryCall dtag state) .zero) (witness ptag ctag state requested formula))

theorem substSound {m n : Nat} (sub : Fin m → Term n) ftag dtag ptag ctag (state requested formula certificate : Term m) :
    substituteFormula sub (sound ftag dtag ptag ctag state requested formula certificate) =
      sound ftag dtag ptag ctag (substitute sub state) (substitute sub requested) (substitute sub formula) (substitute sub certificate) := by
  simp only [sound,substituteFormula,finalCall,unaryCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,substWitness]
theorem weakenSound {ctx : Nat} ftag dtag ptag ctag (state requested formula certificate : Term ctx) :
    GorbowPACore.weaken (sound ftag dtag ptag ctag state requested formula certificate) =
      sound ftag dtag ptag ctag (liftTerm state) (liftTerm requested) (liftTerm formula) (liftTerm certificate) := by
  rw [GorbowPACore.weaken,substSound]
  rfl
theorem soundAt {ctx : Nat} ftag dtag ptag ctag (state requested formula certificate : Term ctx) :
    GorbowStandardInstances.instantiate
      (sound ftag dtag ptag ctag (.var 0) (liftTerm requested) (liftTerm formula) (liftTerm certificate)) state =
      sound ftag dtag ptag ctag state requested formula certificate := by
  simp only [GorbowStandardInstances.instantiate,substSound,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def soundTransport {T : Sentence → Prop} {ctx : Nat} ftag dtag ptag ctag (a b requested formula certificate : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (sound ftag dtag ptag ctag a requested formula certificate)
      (sound ftag dtag ptag ctag b requested formula certificate))) := by
  have h := Derivation.logical (A := T) (.equalityReplace
    (sound ftag dtag ptag ctag (.var 0) (liftTerm requested) (liftTerm formula) (liftTerm certificate)) a b)
  rwa [GorbowPACore.logicalFormula,soundAt,soundAt] at h

theorem rejected {T : Sentence → Prop} {ctx : Nat} ftag dtag ptag ctag (state requested formula certificate : Term ctx)
    (hz : Derivation T (.equal (finalCall ftag state requested formula certificate) .zero)) :
    Nonempty (Derivation T (sound ftag dtag ptag ctag state requested formula certificate)) := by
  let E := Formula.equal (finalCall ftag state requested formula certificate) (.succ .zero)
  let D := Formula.equal (unaryCall dtag state) .zero
  have he : Hilbert.Local T ctx [D,E] E := .hypothesis (by simp)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (HistoryRuleSuffix.SuffixProof.reject _ (witness ptag ctag state requested formula) he (.base hz))))⟩

theorem successful {n ctx : Nat} (p : Program n) (ftag dtag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (sound ftag dtag ptag ctag (successfulState ptag ctag context raw tail lines) requested formula certificate)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let state := successfulState ptag ctag context raw tail lines
  let E := Formula.equal (finalCall ftag state requested formula certificate) (.succ .zero)
  let D := Formula.equal (unaryCall dtag state) .zero
  have he : Hilbert.Local T ctx [D,E] E := .hypothesis (by simp)
  have hd0 : Hilbert.Local T ctx [D,E] D := .hypothesis List.mem_cons_self
  obtain ⟨hfchar⟩ := ComparisonProof.internalFinishCharacterization n p ftag ptag ctag hf hp hc ctx
    context raw tail lines requested formula certificate
  have hfields := Hilbert.Local.mp (.mp (.base (.logical (.andLeft _ _))) (.base hfchar)) he
  have hcontext : Hilbert.Local T ctx [D,E] (.equal requested context) := .mp (.base (.logical (.andLeft _ _))) hfields
  have hformula : Hilbert.Local T ctx [D,E] (.equal formula (.add raw raw)) := .mp (.base (.logical (.andRight _ _))) hfields
  obtain ⟨hr⟩ := HistoryLookup.DestructorProof.decoderCrossPair p dtag ptag true hd hp
    (.succ (HistoryKernel.pairCall ctag (HistoryKernel.pairCall ptag context raw) tail)) lines
  have hlines : Hilbert.Local T ctx [D,E] (.equal lines .zero) :=
    localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hr)) hd0
  have hentry := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag context raw requested raw
    (HistoryOrder.StepProof.localSym _ _ hcontext) (.base (.logical (.reflexive raw)))
  have hhistory := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ctag
    (HistoryKernel.pairCall ptag context raw) tail (HistoryKernel.pairCall ptag requested raw) tail hentry (.base (.logical (.reflexive tail)))
  have hstate := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ lines _ .zero
    (localUnary (.succ (.var 0)) _ _ hhistory) hlines
  have hb : Hilbert.Local T ctx [D,E] (body ptag ctag state requested formula raw tail) :=
    .mp (.mp (.base (.logical (.andIntro _ _))) hformula) hstate
  have hw := Hilbert.Local.mp (.base (introWitness ptag ctag state requested formula raw tail)) hb
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hw))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.ShapeProof
