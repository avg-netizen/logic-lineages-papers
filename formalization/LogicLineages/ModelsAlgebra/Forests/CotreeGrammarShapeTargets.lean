module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShapeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape.Targets
open ForestParseRepresentationBinary ProfileAutomatonEncoding

def ShapeLanguageExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) q w,
    w ∈ (CotreeGrammar.grammar δ q).language ↔
      ∃ s : Shape (Finset Q × Q), Valid s ∧ fold δ Prod.snd s = q ∧
        (word s).map Prod.fst = w

def GraftRunExact : Prop :=
  ∀ (M : Machine) (o : RankedParse.Operation) (I : Type) (r : I → RankedParse.Term)
    (s : Shape I), machineRun M (graft o r s) = fold (M.node o) (machineRun M ∘ r) s

/-- Sound calibration to actual binary grafting, with every repeated leaf retained. -/
def GraftGrammarSound : Prop :=
  ∀ (M : Machine) [DecidableEq M.State] (o : RankedParse.Operation) (I : Type)
    (r : I → RankedParse.Term) (B : I → Finset M.State) (s : Shape I),
    (∀ i, machineRun M (r i) ∈ B i) →
    (word s).map B ∈ (CotreeGrammar.grammar (M.node o) (machineRun M (graft o r s))).language

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape.Targets
