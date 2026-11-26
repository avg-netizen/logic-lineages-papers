module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.FieldsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EntryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix FieldsProof

def rawRightWrapper (tag : Nat) := tag+argumentTag (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => applyOne (HistoryDecoder.decoder true) currentLine) 0
def entryArguments : Fin 2 → Program 3 := Fin.cases lineContext (Fin.cases lineRaw Fin.elim0)
def contextWrapper (tag : Nat) := tag+argumentTag HistoryCodec.pair entryArguments 0
def rawWrapper (tag : Nat) := tag+argumentTag HistoryCodec.pair entryArguments 1
def entryValue {ctx : Nat} (tag : Nat) (line : Term ctx) : Term ctx :=
  pairCall (tag+1) (call (contextWrapper tag+1) (line ::ᵥ nil))
    (call (rawWrapper tag+1) (call (rawRightWrapper (rawWrapper tag)+1) (line ::ᵥ nil) ::ᵥ nil))

theorem contextEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,lineContext⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) (call (tag+1) (line ::ᵥ nil)))) :=
  HistoryAppend.ValueEquationsProof.unaryValues p tag (HistoryDecoder.decoder false) (fun _ : Fin 1 => currentLine) ht _ line
    (currentEquation p _ ptag ctag
      (SixSol20261112.Fuel.Equations.argumentChild p tag (HistoryDecoder.decoder false) (fun _ : Fin 1 => currentLine) ht 0)
      hp hc index fuel h line rest)

theorem rawEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,lineRaw⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest))
        (call (tag+1) (call (rawRightWrapper tag+1) (line ::ᵥ nil) ::ᵥ nil)))) := by
  have hr := SixSol20261112.Fuel.Equations.argumentChild p tag (HistoryDecoder.decoder false)
    (fun _ : Fin 1 => applyOne (HistoryDecoder.decoder true) currentLine) ht 0
  have hl := SixSol20261112.Fuel.Equations.argumentChild p (rawRightWrapper tag) (HistoryDecoder.decoder true)
    (fun _ : Fin 1 => currentLine) hr 0
  apply HistoryAppend.ValueEquationsProof.unaryValues p tag (HistoryDecoder.decoder false) _ ht _
  exact HistoryAppend.ValueEquationsProof.unaryValues p (rawRightWrapper tag) (HistoryDecoder.decoder true)
    (fun _ : Fin 1 => currentLine) hr _ line (currentEquation p _ ptag ctag hl hp hc index fuel h line rest)

theorem entryEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,entry⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) (entryValue tag line))) :=
  HistoryAppend.ValueEquationsProof.binaryValues p tag HistoryCodec.pair entryArguments ht _ _ _
    (contextEquation p (contextWrapper tag) ptag ctag
      (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 0) hp hc index fuel h line rest)
    (rawEquation p (rawWrapper tag) ptag ctag
      (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 1) hp hc index fuel h line rest)

def extendedArguments : Fin 2 → Program 3 := Fin.cases entry (Fin.cases historyPayload Fin.elim0)
def extendedWrapper (tag : Nat) := tag+argumentTag .succ (fun _ : Fin 1 => extendedHistory) 0
def entryWrapper (tag : Nat) := extendedWrapper tag+argumentTag HistoryCodec.cons extendedArguments 0
def outputConsTag (tag : Nat) := extendedWrapper tag+1

def newHistory {ctx : Nat} (tag : Nat) (h line : Term ctx) : Term ctx :=
  HistoryLookup.consCall (outputConsTag tag) (entryValue (entryWrapper tag) line) h

theorem outputConsInstalled {n : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,someExtendedHistory⟩) :
    (nodes p)[outputConsTag tag]? = some ⟨2,HistoryCodec.cons⟩ :=
  SixSol20261112.Fuel.Equations.functionChild p (extendedWrapper tag) HistoryCodec.cons extendedArguments
    (SixSol20261112.Fuel.Equations.argumentChild p tag .succ (fun _ : Fin 1 => extendedHistory) ht 0)

theorem someEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,someExtendedHistory⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) (.succ (newHistory tag h line)))) := by
  have he := SixSol20261112.Fuel.Equations.argumentChild p tag .succ (fun _ : Fin 1 => extendedHistory) ht 0
  have hentry := SixSol20261112.Fuel.Equations.argumentChild p (extendedWrapper tag) HistoryCodec.cons extendedArguments he 0
  have hhist := SixSol20261112.Fuel.Equations.argumentChild p (extendedWrapper tag) HistoryCodec.cons extendedArguments he 1
  obtain ⟨hcons⟩ := HistoryAppend.ValueEquationsProof.binaryValues p (extendedWrapper tag) HistoryCodec.cons extendedArguments he
    (activeArgs ptag ctag index fuel h line rest) (entryValue (entryWrapper tag) line) h
    (entryEquation p (entryWrapper tag) ptag ctag hentry hp hc index fuel h line rest)
    (historyEquation p _ ptag ctag hhist hp index fuel h line rest)
  obtain ⟨hout⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag .succ (fun _ : Fin 1 => extendedHistory) ht _ (newHistory tag h line) ⟨hcons⟩
  have hs := SixSol20261112.Fuel.Equations.functionChild p tag .succ (fun _ : Fin 1 => extendedHistory) ht
  obtain ⟨hstep⟩ := Support.intoRegistry p .succ (tag+1) hs _
    (NamedArithmeticGraph.Equations.successor (tag+1) ctx (newHistory tag h line ::ᵥ nil))
  exact ⟨Logic.trans _ _ _ hout hstep⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EntryProof
