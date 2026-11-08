module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerFinishProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSummaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof InternalParameterizedPathCheckerFinishProof
open InternalPathChecker (triple)
open InternalPathCheckerFinishProof (pairLeft)
open InternalListCodec InternalListCodecSupportProof InternalRawListRecursionSupportProof
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem entryVertexValue (raw previous y vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate))) :
    Nonempty (Derivation body Gamma (programGraph entryVertex vertex (quadruple raw previous y parameter))) := by
  apply compositionValue InternalUnpair.left (fun _ : Fin 1 => .projection 0)
    vertex (quadruple raw previous y parameter) (Fin.cons raw Fin.elim0) (pairLeft raw vertex certificate hp)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 (quadruple raw previous y parameter)

theorem tailRunValue (edge : Program 4) (raw previous y vertex certificate result parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous parameter))) :
    Nonempty (Derivation body Gamma (programGraph (tailRun edge) result (quadruple raw previous y parameter))) := by
  apply compositionValue (finish edge false) (quadruple entryVertex (.projection 2) (.projection 1) (.projection 3))
    result (quadruple raw previous y parameter) (quadruple vertex y previous parameter) hf
  intro i
  exact Fin.cases (entryVertexValue raw previous y vertex certificate parameter hp)
    (Fin.cases (projectionValue 2 (quadruple raw previous y parameter))
      (Fin.cases (projectionValue 1 (quadruple raw previous y parameter))
        (Fin.cases (projectionValue 3 (quadruple raw previous y parameter)) (fun q => Fin.elim0 q)))) i

theorem summaryStepValue (edge : Program 4)
    (raw previous y vertex certificate result state parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous parameter)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph (summaryStep edge) state (quadruple raw previous y parameter))) := by
  apply compositionValue consCode (Fin.cons (.projection 0) (Fin.cons (tailRun edge) Fin.elim0))
    state (quadruple raw previous y parameter) (Fin.cons raw (Fin.cons result Fin.elim0)) hc
  intro i
  exact Fin.cases (projectionValue 0 (quadruple raw previous y parameter))
    (Fin.cases (tailRunValue edge raw previous y vertex certificate result parameter hp hf)
      (fun q => Fin.elim0 q)) i

theorem summaryZero (edge : Program 4) (y parameter : OTerm α) :
    Nonempty (Derivation body Gamma (summaryGraph edge z z y parameter)) :=
  InternalRawListRecursionProof.nilValue InternalRawListRecursion.zero (summaryStep edge)
    z (Fin.cons y (Fin.cons parameter Fin.elim0)) (InternalRawListRecursionSupportProof.constantZero (Fin.cons y (Fin.cons parameter Fin.elim0)))

/-- The summary constructor follows from the literal raw recursor graph
equation, retaining the original pair entry and target parameter. -/
theorem summaryConsValue (edge : Program 4)
    (code raw tail y vertex certificate previous result state parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y parameter)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous parameter)))
    (hs : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (summaryGraph edge state code y parameter)) :=
  InternalRawListRecursionProof.consValue InternalRawListRecursion.zero (summaryStep edge)
    code raw tail previous state (Fin.cons y (Fin.cons parameter Fin.elim0)) hc ht
    (summaryStepValue edge raw previous y vertex certificate result state parameter hp hf hs)

theorem summaryAtValue (edge : Program 4) (x y code state parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (summaryGraph edge state code y parameter))) :
    Nonempty (Derivation body Gamma (programGraph (summaryAt edge) state (quadruple x y code parameter))) := by
  apply compositionValue (summary edge)
    (triple (.projection 2) (.projection 1) (.projection 3))
    state (quadruple x y code parameter) (Fin.cons code (Fin.cons y (Fin.cons parameter Fin.elim0))) h
  intro i
  exact Fin.cases (projectionValue 2 (quadruple x y code parameter))
    (Fin.cases (projectionValue 1 (quadruple x y code parameter))
      (Fin.cases (projectionValue 3 (quadruple x y code parameter)) (fun q => Fin.elim0 q))) i

theorem checkerValue (edge : Program 4) (positive : Bool) (out x y code state parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (summaryGraph edge state code y parameter)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge positive out x y state parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph edge positive out x y code parameter)) := by
  apply compositionValue (finish edge positive) (quadruple (.projection 0) (.projection 1) (summaryAt edge) (.projection 3))
    out (quadruple x y code parameter) (quadruple x y state parameter) hf
  intro i
  exact Fin.cases (projectionValue 0 (quadruple x y code parameter))
    (Fin.cases (projectionValue 1 (quadruple x y code parameter))
      (Fin.cases (summaryAtValue edge x y code state parameter hs)
        (Fin.cases (projectionValue 3 (quadruple x y code parameter)) (fun q => Fin.elim0 q)))) i

theorem checkerRecover (edge : Program 4) (positive : Bool) (out x y code state parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (summaryGraph edge state code y parameter)))
    (h : Nonempty (Derivation body Gamma (checkerGraph edge positive out x y code parameter))) :
    Nonempty (Derivation body Gamma (finishGraph edge positive out x y state parameter)) := by
  apply compositionRecover (finish edge positive) (quadruple (.projection 0) (.projection 1) (summaryAt edge) (.projection 3))
    out (quadruple x y code parameter) (quadruple x y state parameter) h
  intro i
  exact Fin.cases (projectionValue 0 (quadruple x y code parameter))
    (Fin.cases (projectionValue 1 (quadruple x y code parameter))
      (Fin.cases (summaryAtValue edge x y code state parameter hs)
        (Fin.cases (projectionValue 3 (quadruple x y code parameter)) (fun q => Fin.elim0 q)))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSummaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSummaryProof
