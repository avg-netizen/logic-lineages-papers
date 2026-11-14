module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilGraph : Targets.NilGraph := by
  intro body alpha Delta out needle
  constructor
  · intro h
    rw [equalEqn]
    exact valueUnique contains out z ![z,needle] h (containsNil needle)
  · intro h
    rw [equalEqn] at h
    obtain ⟨h⟩ := h
    exact outputTransport contains z out ![z,needle] ⟨symm h⟩ (containsNil needle)

theorem missRecover (code head tail needle out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (he : Nonempty (Derivation body Delta (equal head needle).not))
    (hv : Nonempty (Derivation body Delta (graph2 contains out code needle))) :
    Nonempty (Derivation body Delta (graph2 contains out tail needle)) := by
  apply programCases contains (Fin.cons tail (Fin.cons needle Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [graph2Rename]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  rw [equalEqn] at he
  have he' := renameInto he j Theta hj
  change Nonempty (Derivation body Theta ((eqn head needle).relabel j).not) at he'
  rw [eqnRelabel] at he'
  have hv' := renameInto hv j Theta hj
  rw [graph2Rename] at hv'
  have hr' : Nonempty (Derivation body Theta
      (graph2 contains rest (tail.relabel j) (needle.relabel j))) := hr
  have he'' : Nonempty (Derivation body Theta (equal (head.relabel j) (needle.relabel j)).not) := by
    simpa only [equalEqn] using he'
  have hm := containsMiss (code.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) rest hc' he'' hr'
  have hu := valueUnique contains rest (out.relabel j)
    ![code.relabel j,needle.relabel j] hm hv'
  exact outputTransport contains rest (out.relabel j)
    ![tail.relabel j,needle.relabel j] hu hr'

theorem missGraph : Targets.MissGraph := by
  intro body alpha Delta code head tail needle out hc he
  exact ⟨missRecover code head tail needle out hc he,
    containsMiss code head tail needle out hc he⟩

theorem classRecover (T L D : Program 2)
    (seed candidate parameter list needle : OTerm alpha)
    (hL : Nonempty (Derivation body Delta (graph2 L list seed parameter)))
    (hD : Nonempty (Derivation body Delta (graph2 D needle candidate parameter)))
    (h : Nonempty (Derivation body Delta
      (graph3 (classTest T L D) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta
      (graph2 T (suc z) candidate parameter ⊓ graph2 contains (suc z) list needle)) := by
  let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
  let target : Program 3 := .composition T ![.projection 1,.projection 2]
  let values : Program 3 := .composition L ![.projection 0,.projection 2]
  let decoded : Program 3 := .composition D ![.projection 1,.projection 2]
  obtain ⟨hf⟩ := conjunctionRecover target (.composition contains ![values,decoded]) xs h
  have ht := binaryRecover T (.projection 1) (.projection 2) (suc z) candidate parameter xs
    ⟨Derivation.conjunctionLeft hf⟩ (projectionValue 1 xs) (projectionValue 2 xs)
  have hl := binaryValue L (.projection 0) (.projection 2) list seed parameter xs
    hL (projectionValue 0 xs) (projectionValue 2 xs)
  have hd := binaryValue D (.projection 1) (.projection 2) needle candidate parameter xs
    hD (projectionValue 1 xs) (projectionValue 2 xs)
  have hm := binaryRecover contains values decoded (suc z) list needle xs
    ⟨Derivation.conjunctionRight hf⟩ hl hd
  obtain ⟨ht⟩ := ht
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.conjunctionIntroduction ht hm⟩

theorem classFactor : Targets.ClassFactor := by
  intro T L D body alpha Delta seed candidate parameter list needle hL hD
  constructor
  · exact classRecover T L D seed candidate parameter list needle hL hD
  · rintro ⟨h⟩
    exact actualInternalClassIntroduction T L D body alpha Delta seed candidate parameter list needle
      ⟨Derivation.conjunctionLeft h⟩ hL hD ⟨Derivation.conjunctionRight h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
