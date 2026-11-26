module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.WitnessProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryOrder.SupportProof

def secondBody {ctx : Nat} (tag : Nat) (a code : Term ctx) : Formula (ctx+1) :=
  .equal (HistoryKernel.pairCall tag (liftTerm a) (.var 0)) (liftTerm code)
def firstBody {ctx : Nat} (tag : Nat) (code : Term ctx) : Formula (ctx+1) :=
  .ex (secondBody tag (.var 0) (liftTerm code))

theorem substPair {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
    substitute sub (HistoryKernel.pairCall tag a b) =
      HistoryKernel.pairCall tag (substitute sub a) (substitute sub b) := by
  simp only [HistoryKernel.pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem secondAt {ctx : Nat} tag (a b code : Term ctx) :
    GorbowStandardInstances.instantiate (secondBody tag a code) b =
      .equal (HistoryKernel.pairCall tag a b) code := by
  simp only [GorbowStandardInstances.instantiate,secondBody,substituteFormula,
    substPair,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substSecond {m n : Nat} (sub : Fin m → Term n) tag (a code : Term m) :
    substituteFormula (liftSubstitute sub) (secondBody tag a code) =
      secondBody tag (substitute sub a) (substitute sub code) := by
  simp only [secondBody,substituteFormula,substPair,substituteLift,substitute,
    liftSubstitute,Fin.cases_zero]

theorem firstAt {ctx : Nat} tag (a code : Term ctx) :
    GorbowStandardInstances.instantiate (firstBody tag code) a = .ex (secondBody tag a code) := by
  simp only [GorbowStandardInstances.instantiate,firstBody,substituteFormula,substSecond,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def witnessIntro {T : Sentence → Prop} {ctx : Nat} tag (a b code : Term ctx) :
    Derivation T (.imp (.equal (HistoryKernel.pairCall tag a b) code) (pairSurjective tag code)) := by
  have h2 := existsIntroRule (T := T) (secondBody tag a code) b
  rw [secondAt] at h2
  have h1 := existsIntroRule (T := T) (firstBody tag code) a
  rw [firstAt] at h1
  exact Hilbert.compose h1 h2

theorem substSurjective {m n : Nat} (sub : Fin m → Term n) tag (code : Term m) :
    substituteFormula sub (pairSurjective tag code) = pairSurjective tag (substitute sub code) := by
  simp only [pairSurjective,substituteFormula,substPair,substituteLift,substitute,
    liftSubstitute,Fin.cases_zero,Fin.cases_succ]

theorem surjectiveAt {ctx : Nat} tag (code : Term ctx) :
    GorbowStandardInstances.instantiate (pairSurjective tag (.var 0)) code = pairSurjective tag code := by
  simp only [GorbowStandardInstances.instantiate,substSurjective,substitute,Fin.cases_zero]

theorem weakenSurjective {ctx : Nat} tag (code : Term ctx) :
    GorbowPACore.weaken (pairSurjective tag code) = pairSurjective tag (liftTerm code) := by
  rw [GorbowPACore.weaken,substSurjective]
  rfl

noncomputable def transport {T : Sentence → Prop} {ctx : Nat} tag (a b : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (pairSurjective tag a) (pairSurjective tag b))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (pairSurjective tag (.var 0)) a b)
  rwa [GorbowPACore.logicalFormula,surjectiveAt,surjectiveAt] at h

theorem zeroWitness {n ctx : Nat} (p : GorbowPRProgram.Program n) tag
    (ht : (GorbowPRRegistry.nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (pairSurjective (ctx := ctx) tag .zero)) := by
  obtain ⟨hz⟩ := HistoryLookup.DestructorProof.pairZero (ctx := ctx) p tag ht
  exact ⟨.mp (witnessIntro tag .zero .zero .zero) hz⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.WitnessProof
