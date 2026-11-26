module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.AppendEquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.ValueEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

def headWrapper (tag : Nat) := tag + argumentTag HistoryCodec.cons valueArguments 0
def predWrapper (tag : Nat) := tag + argumentTag HistoryCodec.cons valueArguments 1
def lookupWrapper (tag : Nat) := predWrapper tag + argumentTag HistoryCodec.predecessor (fun _ : Fin 1 => reference) 0
def differenceWrapper (tag : Nat) := lookupWrapper tag + argumentTag HistoryLookup.lookup referenceArguments 0
def tailWrapper (tag : Nat) := differenceWrapper tag + argumentTag HistoryCodec.difference referenceIndexArguments 0

def normalValue {ctx : Nat} (tag : Nat) (count previous : Term ctx) : Term ctx :=
  call (tag+1)
    (call (headWrapper tag+1) (.succ count ::ᵥ nil) ::ᵥ
      call (predWrapper tag+1)
        (call (lookupWrapper tag+1)
          (call (differenceWrapper tag+1)
            (call (tailWrapper tag+1) (.succ count ::ᵥ nil) ::ᵥ count ::ᵥ nil) ::ᵥ previous ::ᵥ nil) ::ᵥ nil) ::ᵥ nil)

theorem unaryValues {n arity ctx : Nat} (p : Program n) tag (f : Program 1) (g : Fin 1 → Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,.composition f g⟩) (args : List.Vector (Term ctx) arity) (v : Term ctx)
    (hv : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 0) args) v))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) (call (tag+1) (v ::ᵥ nil)))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag f g ht args (v ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact hv
  | succ i => exact Fin.elim0 i

theorem binaryValues {n arity ctx : Nat} (p : Program n) tag (f : Program 2) (g : Fin 2 → Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,.composition f g⟩) (args : List.Vector (Term ctx) arity) (a b : Term ctx)
    (ha : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 0) args) a)))
    (hb : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (tag+argumentTag f g 1) args) b))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) (call (tag+1) (a ::ᵥ b ::ᵥ nil)))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag f g ht args (a ::ᵥ b ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ha
  | succ i => cases i using Fin.cases with
    | zero => exact hb
    | succ i => exact Fin.elim0 i

theorem valueNodes {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨3,value⟩) :
    (nodes p)[tag+1]? = some ⟨2,HistoryCodec.cons⟩ ∧
    (nodes p)[headWrapper tag+1]? = some ⟨1,HistoryLookup.head⟩ ∧
    (nodes p)[tailWrapper tag+1]? = some ⟨1,HistoryLookup.tail⟩ ∧
    (nodes p)[differenceWrapper tag+1]? = some ⟨2,HistoryCodec.difference⟩ ∧
    (nodes p)[lookupWrapper tag+1]? = some ⟨2,HistoryLookup.lookup⟩ ∧
    (nodes p)[predWrapper tag+1]? = some ⟨1,HistoryCodec.predecessor⟩ := by
  have hh := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.cons valueArguments ht 0
  have hp := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.cons valueArguments ht 1
  have hl := SixSol20261112.Fuel.Equations.argumentChild p (predWrapper tag) HistoryCodec.predecessor (fun _ : Fin 1 => reference) hp 0
  have hd := SixSol20261112.Fuel.Equations.argumentChild p (lookupWrapper tag) HistoryLookup.lookup referenceArguments hl 0
  have htail := SixSol20261112.Fuel.Equations.argumentChild p (differenceWrapper tag) HistoryCodec.difference referenceIndexArguments hd 0
  exact ⟨SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.cons valueArguments ht,
    SixSol20261112.Fuel.Equations.functionChild p (headWrapper tag) HistoryLookup.head (fun _ : Fin 1 => inputCode) hh,
    SixSol20261112.Fuel.Equations.functionChild p (tailWrapper tag) HistoryLookup.tail (fun _ : Fin 1 => inputCode) htail,
    SixSol20261112.Fuel.Equations.functionChild p (differenceWrapper tag) HistoryCodec.difference referenceIndexArguments hd,
    SixSol20261112.Fuel.Equations.functionChild p (lookupWrapper tag) HistoryLookup.lookup referenceArguments hl,
    SixSol20261112.Fuel.Equations.functionChild p (predWrapper tag) HistoryCodec.predecessor (fun _ : Fin 1 => reference) hp⟩

theorem valueEquation {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨3,value⟩)
    (count previous right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (count ::ᵥ previous ::ᵥ right ::ᵥ nil)) (normalValue tag count previous))) := by
  let args := count ::ᵥ previous ::ᵥ right ::ᵥ nil
  have hh := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.cons valueArguments ht 0
  have hp := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.cons valueArguments ht 1
  have hl := SixSol20261112.Fuel.Equations.argumentChild p (predWrapper tag) HistoryCodec.predecessor (fun _ : Fin 1 => reference) hp 0
  have hd := SixSol20261112.Fuel.Equations.argumentChild p (lookupWrapper tag) HistoryLookup.lookup referenceArguments hl 0
  have htail := SixSol20261112.Fuel.Equations.argumentChild p (differenceWrapper tag) HistoryCodec.difference referenceIndexArguments hd 0
  have hhc := SixSol20261112.Fuel.Equations.argumentChild p (headWrapper tag) HistoryLookup.head (fun _ : Fin 1 => inputCode) hh 0
  have htc := SixSol20261112.Fuel.Equations.argumentChild p (tailWrapper tag) HistoryLookup.tail (fun _ : Fin 1 => inputCode) htail 0
  obtain ⟨hhe⟩ := unaryValues p (headWrapper tag) HistoryLookup.head (fun _ : Fin 1 => inputCode) hh args (.succ count)
    (HistoryDecoder.OuterEquationsProof.successorProjection p _ (0 : Fin 3) hhc args)
  obtain ⟨hte⟩ := unaryValues p (tailWrapper tag) HistoryLookup.tail (fun _ : Fin 1 => inputCode) htail args (.succ count)
    (HistoryDecoder.OuterEquationsProof.successorProjection p _ (0 : Fin 3) htc args)
  have hdp := SixSol20261112.Fuel.Equations.argumentChild p (differenceWrapper tag) HistoryCodec.difference referenceIndexArguments hd 1
  obtain ⟨hde⟩ := binaryValues p (differenceWrapper tag) HistoryCodec.difference referenceIndexArguments hd args
    (call (tailWrapper tag+1) (.succ count ::ᵥ nil)) count ⟨hte⟩
    (SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 3) hdp args)
  have hlp := SixSol20261112.Fuel.Equations.argumentChild p (lookupWrapper tag) HistoryLookup.lookup referenceArguments hl 1
  obtain ⟨hle⟩ := binaryValues p (lookupWrapper tag) HistoryLookup.lookup referenceArguments hl args
    (call (differenceWrapper tag+1) (call (tailWrapper tag+1) (.succ count ::ᵥ nil) ::ᵥ count ::ᵥ nil)) previous ⟨hde⟩
    (SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 3) hlp args)
  obtain ⟨hpe⟩ := unaryValues p (predWrapper tag) HistoryCodec.predecessor (fun _ : Fin 1 => reference) hp args
    (call (lookupWrapper tag+1)
      (call (differenceWrapper tag+1) (call (tailWrapper tag+1) (.succ count ::ᵥ nil) ::ᵥ count ::ᵥ nil) ::ᵥ previous ::ᵥ nil)) ⟨hle⟩
  exact binaryValues p tag HistoryCodec.cons valueArguments ht args
    (call (headWrapper tag+1) (.succ count ::ᵥ nil))
    (call (predWrapper tag+1) (call (lookupWrapper tag+1)
      (call (differenceWrapper tag+1) (call (tailWrapper tag+1) (.succ count ::ᵥ nil) ::ᵥ count ::ᵥ nil) ::ᵥ previous ::ᵥ nil) ::ᵥ nil)) ⟨hhe⟩ ⟨hpe⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.ValueEquationsProof
