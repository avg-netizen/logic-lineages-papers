module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.GuardProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def guardArgs {arity : Nat} (i : Fin arity) (body : Program arity) : Fin 3 → Program arity :=
  Fin.cases (.projection i) (Fin.cases (constant arity 0) (Fin.cases body Fin.elim0))
def bodyTag {arity : Nat} (tag : Nat) (i : Fin arity) (body : Program arity) :=
  tag+argumentTag HistoryCodec.select (guardArgs i body) 2

theorem guardEquation {n arity ctx : Nat} (p : Program n) tag (i : Fin arity) (body : Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,choose (.projection i) (constant arity 0) body⟩)
    (args : List.Vector (Term ctx) arity) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag args) (call (tag+1)
        (args.get i ::ᵥ .zero ::ᵥ call (bodyTag tag i body) args ::ᵥ nil)))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.select (guardArgs i body) ht args
  intro j
  cases j using Fin.cases with
  | zero =>
    exact SixSol20261112.Fuel.Equations.projection p _ i
      (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (guardArgs i body) ht 0) args
  | succ j => cases j using Fin.cases with
    | zero =>
      exact HistoryAppend.TableEquationsProof.zeroEquation p _
        (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (guardArgs i body) ht 1) args
    | succ j => cases j using Fin.cases with
      | zero =>
        exact ⟨.logical (.reflexive _)⟩
      | succ j =>
        exact Fin.elim0 j

theorem guardZero {n arity ctx : Nat} (p : Program n) tag (i : Fin arity) (body : Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,choose (.projection i) (constant arity 0) body⟩)
    (args : List.Vector (Term ctx) arity) (hz : args.get i = .zero) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) .zero)) := by
  obtain ⟨he⟩ := guardEquation p tag i body ht args
  rw [hz] at he
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectZero p (tag+1)
    (SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select (guardArgs i body) ht)
    (.zero : Term ctx) (call (bodyTag tag i body) args)
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem selectBothZero {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (test : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (test ::ᵥ .zero ::ᵥ .zero ::ᵥ nil)) .zero)) := by
  obtain ⟨hg⟩ := HistoryDecoder.SelectGraphProof.selectGraph p tag ht test .zero .zero
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) (Hilbert.identity _))
    (.logical (.andRight _ _))) hg⟩

theorem guardBodyZero {n arity ctx : Nat} (p : Program n) tag (i : Fin arity) (body : Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,choose (.projection i) (constant arity 0) body⟩)
    (args : List.Vector (Term ctx) arity)
    (hb : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (bodyTag tag i body) args) .zero))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) .zero)) := by
  obtain ⟨he⟩ := guardEquation p tag i body ht args
  obtain ⟨hb⟩ := hb
  have hc := Logic.unary (call (tag+1)
    (GorbowSubstitution.liftTerm (args.get i) ::ᵥ .zero ::ᵥ .var 0 ::ᵥ nil)) _ _ hb
  have hc' : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+1) (args.get i ::ᵥ .zero ::ᵥ call (bodyTag tag i body) args ::ᵥ nil))
        (call (tag+1) (args.get i ::ᵥ .zero ::ᵥ .zero ::ᵥ nil))) := by
    simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.liftTerm,
      Support.shiftCancel,GorbowSubstitution.substitute,Fin.cases_zero] using hc
  obtain ⟨hz⟩ := selectBothZero p (tag+1)
    (SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select (guardArgs i body) ht) (args.get i)
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ hc' hz)⟩

def mpGuard : Program 4 :=
  let a : Program 4 := .projection 2
  let b : Program 4 := .projection 3
  conjunction (applyTwo equalCode (entryPart false a) (.projection 0))
    (conjunction (applyTwo equalCode (entryPart false b) (.projection 0))
      (applyTwo equalCode (entryPart true a)
        (applyTwo HistoryCodec.cons (constant 4 7)
          (applyTwo HistoryAppend.append (entryPart true b) (.projection 1)))))
def mpSecond : Program 4 := choose (.projection 3) (constant 4 0) mpGuard

def generalizeGuard : Program 3 :=
  conjunction (applyTwo equalCode (entryPart false (.projection 2)) (applyOne .succ (.projection 0)))
    (applyTwo equalCode (.projection 1) (applyTwo HistoryCodec.cons (constant 3 10) (entryPart true (.projection 2))))

theorem mpZeroLeft {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨4,mpBody⟩) (context raw b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (context ::ᵥ raw ::ᵥ .zero ::ᵥ b ::ᵥ nil)) .zero)) :=
  guardZero p tag (2 : Fin 4) mpSecond ht _ rfl

theorem mpZeroRight {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨4,mpBody⟩) (context raw a : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (context ::ᵥ raw ::ᵥ a ::ᵥ .zero ::ᵥ nil)) .zero)) := by
  have hi := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select
    (guardArgs (2 : Fin 4) mpSecond) ht 2
  exact guardBodyZero p tag (2 : Fin 4) mpSecond ht _
    (guardZero p (bodyTag tag (2 : Fin 4) mpSecond) (3 : Fin 4) mpGuard hi _ rfl)

theorem generalizeZero {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,generalizeBody⟩) (context raw : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (context ::ᵥ raw ::ᵥ .zero ::ᵥ nil)) .zero)) :=
  guardZero p tag (2 : Fin 3) generalizeGuard ht _ rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.GuardProof
