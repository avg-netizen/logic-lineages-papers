module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerFinishProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSummaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalPathChecker InternalPathCheckerSyntaxProof InternalPathCheckerFinishProof
open InternalListCodec InternalListCodecSupportProof InternalRawListRecursionSupportProof
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem entryVertexValue (raw previous y vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate))) :
    Nonempty (Derivation body Gamma (programGraph entryVertex vertex (triple raw previous y))) := by
  apply compositionValue InternalUnpair.left (fun _ : Fin 1 => .projection 0)
    vertex (triple raw previous y) (Fin.cons raw Fin.elim0) (pairLeft raw vertex certificate hp)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 (triple raw previous y)

theorem tailRunValue (edge : Program 3) (raw previous y vertex certificate result : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous))) :
    Nonempty (Derivation body Gamma (programGraph (tailRun edge) result (triple raw previous y))) := by
  apply compositionValue (finish edge false) (triple entryVertex (.projection 2) (.projection 1))
    result (triple raw previous y) (triple vertex y previous) hf
  intro i
  exact Fin.cases (entryVertexValue raw previous y vertex certificate hp)
    (Fin.cases (projectionValue 2 (triple raw previous y))
      (Fin.cases (projectionValue 1 (triple raw previous y)) (fun q => Fin.elim0 q))) i

theorem summaryStepValue (edge : Program 3)
    (raw previous y vertex certificate result state : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph (summaryStep edge) state (triple raw previous y))) := by
  apply compositionValue consCode (Fin.cons (.projection 0) (Fin.cons (tailRun edge) Fin.elim0))
    state (triple raw previous y) (Fin.cons raw (Fin.cons result Fin.elim0)) hc
  intro i
  exact Fin.cases (projectionValue 0 (triple raw previous y))
    (Fin.cases (tailRunValue edge raw previous y vertex certificate result hp hf)
      (fun q => Fin.elim0 q)) i

theorem summaryZero (edge : Program 3) (y : OTerm α) :
    Nonempty (Derivation body Gamma (summaryGraph edge z z y)) :=
  InternalRawListRecursionProof.nilValue InternalRawListRecursion.zero (summaryStep edge)
    z (Fin.cons y Fin.elim0) (InternalRawListRecursionSupportProof.constantZero (Fin.cons y Fin.elim0))

/-- The summary constructor follows from the literal raw recursor graph
equation, retaining the original pair entry and target parameter. -/
theorem summaryConsValue (edge : Program 3)
    (code raw tail y vertex certificate previous result state : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous)))
    (hs : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (summaryGraph edge state code y)) :=
  InternalRawListRecursionProof.consValue InternalRawListRecursion.zero (summaryStep edge)
    code raw tail previous state (Fin.cons y Fin.elim0) hc ht
    (summaryStepValue edge raw previous y vertex certificate result state hp hf hs)

theorem summaryAtValue (edge : Program 3) (x y code state : OTerm α)
    (h : Nonempty (Derivation body Gamma (summaryGraph edge state code y))) :
    Nonempty (Derivation body Gamma (programGraph (summaryAt edge) state (triple x y code))) := by
  apply compositionValue (summary edge)
    (Fin.cons (.projection 2) (Fin.cons (.projection 1) Fin.elim0))
    state (triple x y code) (Fin.cons code (Fin.cons y Fin.elim0)) h
  intro i
  exact Fin.cases (projectionValue 2 (triple x y code))
    (Fin.cases (projectionValue 1 (triple x y code)) (fun q => Fin.elim0 q)) i

theorem checkerValue (edge : Program 3) (positive : Bool) (out x y code state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (summaryGraph edge state code y)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge positive out x y state))) :
    Nonempty (Derivation body Gamma (checkerGraph edge positive out x y code)) := by
  apply compositionValue (finish edge positive) (triple (.projection 0) (.projection 1) (summaryAt edge))
    out (triple x y code) (triple x y state) hf
  intro i
  exact Fin.cases (projectionValue 0 (triple x y code))
    (Fin.cases (projectionValue 1 (triple x y code))
      (Fin.cases (summaryAtValue edge x y code state hs) (fun q => Fin.elim0 q))) i

theorem checkerRecover (edge : Program 3) (positive : Bool) (out x y code state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (summaryGraph edge state code y)))
    (h : Nonempty (Derivation body Gamma (checkerGraph edge positive out x y code))) :
    Nonempty (Derivation body Gamma (finishGraph edge positive out x y state)) := by
  apply compositionRecover (finish edge positive) (triple (.projection 0) (.projection 1) (summaryAt edge))
    out (triple x y code) (triple x y state) h
  intro i
  exact Fin.cases (projectionValue 0 (triple x y code))
    (Fin.cases (projectionValue 1 (triple x y code))
      (Fin.cases (summaryAtValue edge x y code state hs) (fun q => Fin.elim0 q))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSummaryProof
