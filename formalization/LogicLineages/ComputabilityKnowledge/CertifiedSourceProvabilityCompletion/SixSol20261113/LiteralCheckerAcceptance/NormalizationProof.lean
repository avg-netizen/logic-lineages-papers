module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.NormalizationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAuxiliaries

 theorem fourValues {n arity ctx : Nat} (p : Program n) (tag : Nat) (f : Program 4) (g : Fin 4 → Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,.composition f g⟩) (args : List.Vector (Term ctx) arity) (a b c d : Term ctx)
    (ha : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 0) args) a)))
    (hb : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 1) args) b)))
    (hc : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 2) args) c)))
    (hd : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 3) args) d))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) (call (tag+1) (a ::ᵥ b ::ᵥ c ::ᵥ d ::ᵥ nil)))) := by
  apply Equations.compositionValues p tag f g ht args (a ::ᵥ b ::ᵥ c ::ᵥ d ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ha
  | succ i => cases i using Fin.cases with
    | zero => exact hb
    | succ i => cases i using Fin.cases with
      | zero => exact hc
      | succ i => cases i using Fin.cases with
        | zero => exact hd
        | succ i => exact Fin.elim0 i

 def args {ctx : Nat} (index fuel context formula certificate : Term ctx) : List.Vector (Term ctx) 5 :=
  index ::ᵥ fuel ::ᵥ context ::ᵥ formula ::ᵥ certificate ::ᵥ nil

 theorem boundArgument {n ctx : Nat} (p : Program n) (tag : Nat)
    (ht : (nodes p)[tag]? = some ⟨5,SixSol20261112.HistoryMachine.boundArgument bound⟩)
    (index fuel context formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args index fuel context formula certificate)) certificate)) := by
  have hp := Equations.argumentChild p tag bound (fun _ : Fin 1 => (.projection (4 : Fin 5))) ht 0
  have hb := Equations.functionChild p tag bound (fun _ : Fin 1 => (.projection (4 : Fin 5))) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag bound _ ht
    (args index fuel context formula certificate) certificate (Equations.projection p _ (4 : Fin 5) hp _)
  obtain ⟨hb⟩ := InitialProof.internalBound n p _ hb ctx certificate
  exact ⟨Logic.trans _ _ _ he hb⟩

 theorem initialArgument {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (ht : (nodes p)[tag]? = some ⟨5,SixSol20261112.HistoryMachine.initialArgument initial⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (index fuel context formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args index fuel context formula certificate))
        (HistoryKernel.pairCall ptag (.succ .zero) certificate))) := by
  have hproj := Equations.argumentChild p tag initial (fun _ : Fin 1 => (.projection (4 : Fin 5))) ht 0
  have hi := Equations.functionChild p tag initial (fun _ : Fin 1 => (.projection (4 : Fin 5))) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag initial _ ht
    (args index fuel context formula certificate) certificate (Equations.projection p _ (4 : Fin 5) hproj _)
  obtain ⟨hi⟩ := InitialProof.internalInitial n p _ ptag hi hp ctx certificate
  exact ⟨Logic.trans _ _ _ he hi⟩

 theorem loopEquation {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨5,SixSol20261112.HistoryMachine.loop (HistoryKernel.kernel v l a x) bound initial⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (index fuel context formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args index fuel context formula certificate))
        (runCall (tag+1) ptag index fuel certificate))) := by
  let k := HistoryKernel.kernel v l a x
  let g := SixSol20261112.HistoryMachine.loopArguments bound initial
  apply fourValues p tag (SixSol20261112.HistoryMachine.iterator k) g ht _
  · exact boundArgument p _ (Equations.argumentChild p tag _ g ht 0) index fuel context formula certificate
  · exact initialArgument p _ ptag (Equations.argumentChild p tag _ g ht 1) hp index fuel context formula certificate
  · exact Equations.projection p _ (0 : Fin 5) (Equations.argumentChild p tag _ g ht 2) _
  · exact Equations.projection p _ (1 : Fin 5) (Equations.argumentChild p tag _ g ht 3) _

 theorem internalCoreNormalization : Targets.InternalCoreNormalization := by
  intro n p qtag ptag v l a x ht hp ctx index fuel context formula certificate
  let k := HistoryKernel.kernel v l a x
  let g := SixSol20261112.HistoryMachine.checkerArguments k bound initial
  have hloop := Equations.argumentChild p qtag finalizer g ht 0
  have he := loopEquation p _ ptag v l a x hloop hp index fuel context formula certificate
  have he' : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (qtag+argumentTag finalizer g 0) (args index fuel context formula certificate))
        (runCall (qtag+iteratorOffset v l a x) ptag index fuel certificate))) := by
    simpa only [iteratorOffset,Nat.add_assoc] using he
  exact fourValues p qtag finalizer g ht (args index fuel context formula certificate)
    _ context formula certificate he'
    (Equations.projection p _ (2 : Fin 5) (Equations.argumentChild p qtag finalizer g ht 1) _)
    (Equations.projection p _ (3 : Fin 5) (Equations.argumentChild p qtag finalizer g ht 2) _)
    (Equations.projection p _ (4 : Fin 5) (Equations.argumentChild p qtag finalizer g ht 3) _)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.NormalizationProof
