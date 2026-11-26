module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EntryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.TransitionEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix FieldsProof EntryProof

/-- All offsets below are actual composition children in the literal kernel. -/
def kernelArguments (v l a : Program 1) (x : Program 3) : Fin 3 → Program 3 :=
  Fin.cases stateLines (Fin.cases (.projection 0) (Fin.cases (nextState v l a x) Fin.elim0))
def nextArguments (v l a : Program 1) (x : Program 3) : Fin 2 → Program 3 :=
  Fin.cases (nextOption v l a x) (Fin.cases remainingLines Fin.elim0)
def optionArguments (v l a : Program 1) (x : Program 3) : Fin 3 → Program 3 :=
  Fin.cases stateOption (Fin.cases (constant 3 0) (Fin.cases (acceptedOption v l a x) Fin.elim0))
def acceptedArguments (v l a : Program 1) (x : Program 3) : Fin 3 → Program 3 :=
  Fin.cases (acceptedTest v l a x) (Fin.cases (constant 3 0) (Fin.cases someExtendedHistory Fin.elim0))
def testArguments (v l a : Program 1) (x : Program 3) : Fin 2 → Program 3 :=
  Fin.cases (checkedLine v l a x) (Fin.cases (constant 3 1) Fin.elim0)

def nextTag (tag : Nat) (v l a : Program 1) (x : Program 3) := tag+argumentTag HistoryCodec.select (kernelArguments v l a x) 2
def optionTag (tag : Nat) (v l a : Program 1) (x : Program 3) := nextTag tag v l a x+argumentTag HistoryCodec.pair (nextArguments v l a x) 0
def acceptedTag (tag : Nat) (v l a : Program 1) (x : Program 3) := optionTag tag v l a x+argumentTag HistoryCodec.select (optionArguments v l a x) 2
def testTag (tag : Nat) (v l a : Program 1) (x : Program 3) := acceptedTag tag v l a x+argumentTag HistoryCodec.select (acceptedArguments v l a x) 0
def someTag (tag : Nat) (v l a : Program 1) (x : Program 3) := acceptedTag tag v l a x+argumentTag HistoryCodec.select (acceptedArguments v l a x) 2
def checkTag (tag : Nat) (v l a : Program 1) (x : Program 3) := testTag tag v l a x+argumentTag equalCode (testArguments v l a x) 0

theorem checkedEquation {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,checkedLine v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest))
        (HistoryDispatcher.dispatcherCall (tag+1) index fuel h line))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag (HistoryDispatcher.lineDispatcher v l a x) dispatcherArguments ht
    (activeArgs ptag ctag index fuel h line rest) (index ::ᵥ fuel ::ᵥ h ::ᵥ line ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero =>
      exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 3)
        (SixSol20261112.Fuel.Equations.argumentChild p tag _ dispatcherArguments ht 0) _
  | succ i => cases i using Fin.cases with
    | zero =>
        exact SixSol20261112.Fuel.Equations.projection p _ (2 : Fin 3)
          (SixSol20261112.Fuel.Equations.argumentChild p tag _ dispatcherArguments ht 1) _
    | succ i => cases i using Fin.cases with
      | zero =>
          exact historyEquation p _ ptag ctag
            (SixSol20261112.Fuel.Equations.argumentChild p tag _ dispatcherArguments ht 2) hp index fuel h line rest
      | succ i => cases i using Fin.cases with
        | zero =>
            exact currentEquation p _ ptag ctag
              (SixSol20261112.Fuel.Equations.argumentChild p tag _ dispatcherArguments ht 3) hp hc index fuel h line rest
        | succ i => exact Fin.elim0 i

/-- Universal arity-three composition normalization, no native evaluation. -/
theorem threeValues {n arity ctx : Nat} (p : Program n) tag (f : Program 3) (g : Fin 3 → Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,.composition f g⟩) (args : List.Vector (Term ctx) arity) (a b c : Term ctx)
    (ha : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 0) args) a)))
    (hb : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 1) args) b)))
    (hc : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 2) args) c))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) (call (tag+1) (a ::ᵥ b ::ᵥ c ::ᵥ nil)))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag f g ht args (a ::ᵥ b ::ᵥ c ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ha
  | succ i => cases i using Fin.cases with
    | zero => exact hb
    | succ i => cases i using Fin.cases with
      | zero => exact hc
      | succ i => exact Fin.elim0 i

theorem nextInstalled {n : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) :
    (nodes p)[nextTag tag v l a x]? = some ⟨3,nextState v l a x⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p (tag) HistoryCodec.select (kernelArguments v l a x) ht 2

theorem optionInstalled {n : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) :
    (nodes p)[optionTag tag v l a x]? = some ⟨3,nextOption v l a x⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p (nextTag tag v l a x) HistoryCodec.pair (nextArguments v l a x) (nextInstalled p tag v l a x ht) 0

theorem acceptedInstalled {n : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) :
    (nodes p)[acceptedTag tag v l a x]? = some ⟨3,acceptedOption v l a x⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p (optionTag tag v l a x) HistoryCodec.select (optionArguments v l a x) (optionInstalled p tag v l a x ht) 2

theorem testInstalled {n : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) :
    (nodes p)[testTag tag v l a x]? = some ⟨3,acceptedTest v l a x⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p (acceptedTag tag v l a x) HistoryCodec.select (acceptedArguments v l a x) (acceptedInstalled p tag v l a x ht) 0

theorem someInstalled {n : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) :
    (nodes p)[someTag tag v l a x]? = some ⟨3,someExtendedHistory⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p (acceptedTag tag v l a x) HistoryCodec.select (acceptedArguments v l a x) (acceptedInstalled p tag v l a x ht) 2

theorem checkInstalled {n : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) :
    (nodes p)[checkTag tag v l a x]? = some ⟨3,checkedLine v l a x⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p (testTag tag v l a x) equalCode (testArguments v l a x) (testInstalled p tag v l a x ht) 0

def dispatcherTag (tag : Nat) (v l a : Program 1) (x : Program 3) := checkTag tag v l a x+1
def equalityTag (tag : Nat) (v l a : Program 1) (x : Program 3) := testTag tag v l a x+1
def selectorTag (tag : Nat) (v l a : Program 1) (x : Program 3) := acceptedTag tag v l a x+1
def outputPairTag (tag : Nat) (v l a : Program 1) (x : Program 3) := nextTag tag v l a x+1

def optionValue {ctx : Nat} (tag : Nat) (v l a : Program 1) (x : Program 3) (index fuel h line : Term ctx) : Term ctx :=
  call (selectorTag tag v l a x)
    (pairCall (equalityTag tag v l a x)
      (HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line) (.succ .zero) ::ᵥ
      .zero ::ᵥ .succ (newHistory (someTag tag v l a x) h line) ::ᵥ nil)
def normal {ctx : Nat} (tag : Nat) (v l a : Program 1) (x : Program 3) (index fuel h line rest : Term ctx) : Term ctx :=
  pairCall (outputPairTag tag v l a x) (optionValue tag v l a x index fuel h line) rest

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.TransitionEquationsProof
