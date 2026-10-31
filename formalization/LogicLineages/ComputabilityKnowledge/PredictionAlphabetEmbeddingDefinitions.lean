module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeCodeDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbedding

def liftAction : PredictionTapeTable.Action → PredictionFiniteAlphabet.Action
  | .inl b => .inl b
  | .inr a => .inr (PredictionTapeTable.symbolIndex a)

def liftTable (p : PredictionTapeTable.Table) : PredictionFiniteAlphabet.Table :=
  (0, p.1, p.2.map (fun o => o.map (fun x => (x.1, liftAction x.2))))

def liftRaw (c : PredictionTapeTable.Raw) : PredictionFiniteAlphabet.Raw :=
  (c.1, PredictionTapeTable.symbolIndex c.2.1,
    c.2.2.1.map PredictionTapeTable.symbolIndex,
    c.2.2.2.map PredictionTapeTable.symbolIndex)

def liftCode (code : Nat) : Nat :=
  Encodable.encode (liftTable (PredictionTapeTable.decodeTable code))

end LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbedding
