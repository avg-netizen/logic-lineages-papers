module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.InitialProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.FieldsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

def args {ctx : Nat} (ptag : Nat) (option lines requested formula certificate : Term ctx) : List.Vector (Term ctx) 4 :=
  HistoryKernel.pairCall ptag option lines ::ᵥ requested ::ᵥ formula ::ᵥ certificate ::ᵥ nil

def successfulArgs {ctx : Nat} (ptag ctag : Nat) (context raw tail lines requested formula certificate : Term ctx) : List.Vector (Term ctx) 4 :=
  successfulState ptag ctag context raw tail lines ::ᵥ requested ::ᵥ formula ::ᵥ certificate ::ᵥ nil

theorem optionEquation {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,optionField⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (option lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args ptag option lines requested formula certificate)) option)) := by
  have hd := Equations.functionChild p tag (HistoryDecoder.decoder false) (fun _ : Fin 1 => .projection (0 : Fin 4)) ht
  have hv := Equations.argumentChild p tag (HistoryDecoder.decoder false) (fun _ : Fin 1 => .projection (0 : Fin 4)) ht 0
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag (HistoryDecoder.decoder false) _ ht
    (args ptag option lines requested formula certificate) (HistoryKernel.pairCall ptag option lines)
    (Equations.projection p _ (0 : Fin 4) hv _)
  obtain ⟨hi⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (tag+1) ptag false hd hp option lines
  exact ⟨Logic.trans _ _ _ he hi⟩

theorem historyEquation {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,historyField⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (history lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args ptag (.succ history) lines requested formula certificate)) history)) := by
  have ho := Equations.argumentChild p tag HistoryCodec.predecessor (fun _ : Fin 1 => optionField) ht 0
  have hpred := Equations.functionChild p tag HistoryCodec.predecessor (fun _ : Fin 1 => optionField) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag HistoryCodec.predecessor _ ht
    (args ptag (.succ history) lines requested formula certificate) (.succ history)
    (optionEquation p _ ptag ho hp (.succ history) lines requested formula certificate)
  obtain ⟨hi⟩ := HistoryDifference.EquationsProof.predecessorSuccessor n p (tag+1) hpred ctx history
  exact ⟨Logic.trans _ _ _ he hi⟩

theorem entryEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,entryField⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (successfulArgs ptag ctag context raw tail lines requested formula certificate))
        (HistoryKernel.pairCall ptag context raw))) := by
  have hh := Equations.argumentChild p tag HistoryLookup.head (fun _ : Fin 1 => historyField) ht 0
  have hhead := Equations.functionChild p tag HistoryLookup.head (fun _ : Fin 1 => historyField) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag HistoryLookup.head _ ht
    (successfulArgs ptag ctag context raw tail lines requested formula certificate)
    (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail)
    (historyEquation p _ ptag hh hp _ lines requested formula certificate)
  obtain ⟨hi⟩ := HistoryLookup.DestructorProof.internalHeadCons n p (tag+1) ctag hhead hc ctx (HistoryKernel.pairCall ptag context raw) tail
  exact ⟨Logic.trans _ _ _ he hi⟩

theorem entryPartEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat) right
    (ht : (nodes p)[tag]? = some ⟨4,applyOne (HistoryDecoder.decoder right) entryField⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (successfulArgs ptag ctag context raw tail lines requested formula certificate))
        (HistoryDecoder.StepNormalProof.chosen right context raw))) := by
  have hh := Equations.argumentChild p tag (HistoryDecoder.decoder right) (fun _ : Fin 1 => entryField) ht 0
  have hd := Equations.functionChild p tag (HistoryDecoder.decoder right) (fun _ : Fin 1 => entryField) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag (HistoryDecoder.decoder right) _ ht
    (successfulArgs ptag ctag context raw tail lines requested formula certificate) (HistoryKernel.pairCall ptag context raw)
    (entryEquation p _ ptag ctag hh hp hc context raw tail lines requested formula certificate)
  obtain ⟨hi⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (tag+1) ptag right hd hp context raw
  exact ⟨Logic.trans _ _ _ he hi⟩

def doubleArguments : Fin 2 → Program 4 := Fin.cases rawField (Fin.cases rawField Fin.elim0)

theorem doubledEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,doubledRaw⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (successfulArgs ptag ctag context raw tail lines requested formula certificate)) (.add raw raw))) := by
  have h0 := Equations.argumentChild p tag HistoryCodec.add doubleArguments ht 0
  have h1 := Equations.argumentChild p tag HistoryCodec.add doubleArguments ht 1
  have ha := Equations.functionChild p tag HistoryCodec.add doubleArguments ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.binaryValues p tag HistoryCodec.add doubleArguments ht
    (successfulArgs ptag ctag context raw tail lines requested formula certificate) raw raw
    (entryPartEquation p _ ptag ctag true h0 hp hc context raw tail lines requested formula certificate)
    (entryPartEquation p _ ptag ctag true h1 hp hc context raw tail lines requested formula certificate)
  obtain ⟨hi⟩ := HistoryCodec.AddProof.internalAdd n p (tag+1) ha ctx raw raw
  exact ⟨Logic.trans _ _ _ he hi⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.FieldsProof
