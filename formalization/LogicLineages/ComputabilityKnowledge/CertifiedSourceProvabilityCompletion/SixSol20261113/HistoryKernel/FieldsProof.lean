module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.FieldsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

def activeArgs {ctx : Nat} (ptag ctag : Nat) (index fuel h line rest : Term ctx) : List.Vector (Term ctx) 3 :=
  activeState ptag ctag h line rest ::ᵥ index ::ᵥ fuel ::ᵥ nil

theorem optionEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,stateOption⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) (.succ h))) := by
  have hd := SixSol20261112.Fuel.Equations.functionChild p tag (HistoryDecoder.decoder false) (fun _ : Fin 1 => .projection (0 : Fin 3)) ht
  have hv := SixSol20261112.Fuel.Equations.argumentChild p tag (HistoryDecoder.decoder false) (fun _ : Fin 1 => .projection (0 : Fin 3)) ht 0
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag (HistoryDecoder.decoder false) _ ht
    (activeArgs ptag ctag index fuel h line rest) (activeState ptag ctag h line rest)
    (SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 3) hv _)
  obtain ⟨hc⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (tag+1) ptag false hd hp (.succ h) (HistoryLookup.consCall ctag line rest)
  exact ⟨Logic.trans _ _ _ he hc⟩

theorem linesEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,stateLines⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) (HistoryLookup.consCall ctag line rest))) := by
  have hd := SixSol20261112.Fuel.Equations.functionChild p tag (HistoryDecoder.decoder true) (fun _ : Fin 1 => .projection (0 : Fin 3)) ht
  have hv := SixSol20261112.Fuel.Equations.argumentChild p tag (HistoryDecoder.decoder true) (fun _ : Fin 1 => .projection (0 : Fin 3)) ht 0
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag (HistoryDecoder.decoder true) _ ht
    (activeArgs ptag ctag index fuel h line rest) (activeState ptag ctag h line rest)
    (SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 3) hv _)
  obtain ⟨hc⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (tag+1) ptag true hd hp (.succ h) (HistoryLookup.consCall ctag line rest)
  exact ⟨Logic.trans _ _ _ he hc⟩

theorem currentEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,currentLine⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) line)) := by
  have hs := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryLookup.head (fun _ : Fin 1 => stateLines) ht 0
  have hh := SixSol20261112.Fuel.Equations.functionChild p tag HistoryLookup.head (fun _ : Fin 1 => stateLines) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag HistoryLookup.head _ ht
    (activeArgs ptag ctag index fuel h line rest) (HistoryLookup.consCall ctag line rest)
    (linesEquation p _ ptag ctag hs hp index fuel h line rest)
  obtain ⟨hv⟩ := HistoryLookup.DestructorProof.internalHeadCons n p (tag+1) ctag hh hc ctx line rest
  exact ⟨Logic.trans _ _ _ he hv⟩

theorem remainingEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,remainingLines⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) rest)) := by
  have hs := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryLookup.tail (fun _ : Fin 1 => stateLines) ht 0
  have hh := SixSol20261112.Fuel.Equations.functionChild p tag HistoryLookup.tail (fun _ : Fin 1 => stateLines) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag HistoryLookup.tail _ ht
    (activeArgs ptag ctag index fuel h line rest) (HistoryLookup.consCall ctag line rest)
    (linesEquation p _ ptag ctag hs hp index fuel h line rest)
  obtain ⟨hv⟩ := HistoryLookup.DestructorProof.internalTailCons n p (tag+1) ctag hh hc ctx line rest
  exact ⟨Logic.trans _ _ _ he hv⟩

theorem historyEquation {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,historyPayload⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (activeArgs ptag ctag index fuel h line rest)) h)) := by
  have hs := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.predecessor (fun _ : Fin 1 => stateOption) ht 0
  have hh := SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.predecessor (fun _ : Fin 1 => stateOption) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag HistoryCodec.predecessor _ ht
    (activeArgs ptag ctag index fuel h line rest) (.succ h)
    (optionEquation p _ ptag ctag hs hp index fuel h line rest)
  obtain ⟨hv⟩ := HistoryDifference.EquationsProof.predecessorSuccessor n p (tag+1) hh ctx h
  exact ⟨Logic.trans _ _ _ he hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.FieldsProof
