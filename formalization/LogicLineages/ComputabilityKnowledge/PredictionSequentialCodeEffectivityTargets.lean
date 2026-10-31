module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivityDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivity.Targets
open PredictionSequentialCodeCodec

def ConstructorPrimitiveRecursive : Prop :=
  Primrec₂ Turing.ToPartrec.Code.cons ∧ Primrec₂ Turing.ToPartrec.Code.comp ∧ Primrec₂ Turing.ToPartrec.Code.case ∧ Primrec Turing.ToPartrec.Code.fix

def DecodePrimitiveRecursive : Prop := Primrec decode

def CasesPrimitiveRecursive : Prop := ∀ (α : Type) [Primcodable α]
  (leaf : Nat → α) (branch : Nat → Code → Code → α),
  Primrec leaf → Primrec (fun p : Nat × Code × Code => branch p.1 p.2.1 p.2.2) →
    Primrec (cases leaf branch)

def StructuralFoldPrimitiveRecursive : Prop := ∀ (α : Type) [Primcodable α]
  (leaf : Nat → α) (branch : Nat → α → α → α),
  Primrec leaf → Primrec (fun p : Nat × α × α => branch p.1 p.2.1 p.2.2) →
    Primrec (termFold leaf branch)
end LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivity.Targets
