module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryLengthOffset ConstructorSupportProof

theorem lineComputes {n ctx : Nat} (p : Program n) (ptag : Nat)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (args : List.Vector (Term ctx) 3) :
    Computes p lineProgram args (lineValue ptag (args.get 0) (args.get 1) (args.get 2)) := by
  apply binary p args HistoryCodec.pair ptag hp
  · exact projection p args 0
  · apply binary p args HistoryCodec.pair ptag hp
    · exact projection p args 1
    · apply binary p args HistoryCodec.pair ptag hp
      · exact constantValue p args 2
      · apply binary p args HistoryCodec.pair ptag hp
        · exact constantValue p args 0
        · apply binary p args HistoryCodec.pair ptag hp
          · exact constantValue p args 0
          · apply binary p args HistoryCodec.pair ptag hp
            · exact projection p args 2
            · exact constantValue p args 0

theorem newLineComputes {n ctx : Nat} (p : Program n) (ltag ptag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (args : List.Vector (Term ctx) 4) :
    Computes p newLine args (lineValue ptag (args.get 0) (args.get 1) (lengthCall ltag (args.get 3))) := by
  intro tag ht
  let values := args.get 0 ::ᵥ args.get 1 ::ᵥ lengthCall ltag (args.get 3) ::ᵥ nil
  have hv : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+argumentTag lineProgram lineArguments i) args) (values.get i))) := by
    intro i
    cases i using Fin.cases with
    | zero => exact projection p args 0 _ (SixSol20261112.Fuel.Equations.argumentChild p tag lineProgram lineArguments ht 0)
    | succ i => cases i using Fin.cases with
      | zero => exact projection p args 1 _ (SixSol20261112.Fuel.Equations.argumentChild p tag lineProgram lineArguments ht 1)
      | succ i => cases i using Fin.cases with
        | zero =>
          exact unary p args lengthProgram ltag hl (.projection 3) (args.get 3) (projection p args 3) _
            (SixSol20261112.Fuel.Equations.argumentChild p tag lineProgram lineArguments ht 2)
        | succ i => exact Fin.elim0 i
  obtain ⟨he⟩ := SixSol20261112.Fuel.Equations.compositionValues p tag lineProgram lineArguments ht args values hv
  obtain ⟨hline⟩ := lineComputes p ptag hp values (tag+1) (SixSol20261112.Fuel.Equations.functionChild p tag lineProgram lineArguments ht)
  exact ⟨Logic.trans _ _ _ he hline⟩

theorem internalConstructor : Targets.InternalConstructor := by
  intro n p tag ltag atag ptag ctag ht hl ha hp hc ctx context raw imp ant
  let args := context ::ᵥ raw ::ᵥ imp ::ᵥ ant ::ᵥ nil
  have h : Computes p constructor args
      (HistoryAppend.appendCall atag (HistoryAppend.appendCall atag imp ant)
        (HistoryLookup.consCall ctag (lineValue ptag context raw (lengthCall ltag ant)) .zero)) := by
    apply binary p args HistoryAppend.append atag ha
    · apply binary p args HistoryAppend.append atag ha
      · exact projection p args 2
      · exact projection p args 3
    · apply binary p args HistoryCodec.cons ctag hc
      · exact newLineComputes p ltag ptag hl hp args
      · exact constantValue p args 0
  exact h tag ht
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorProof
