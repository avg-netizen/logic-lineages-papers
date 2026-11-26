module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.NumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.NumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalPositiveUnfoldingSupportProof InternalQuotientComparisonProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem numbered : Targets.InternalNumbered := by
  intro n arity body alpha Delta V node code param source k head tau base ts extras symbols types t0 h1 t1 h2 t2 h3 t3 hv hn hp hs hc0 hc1 hc2 hc3
  apply programCases OriginalHeadEncodingBridge.encodeHead (Fin.cons head Fin.elim0) _
  intro beta j Theta encoded hj he
  simp only [consTermRename,emptyRename] at he
  have hvj := renameInto hv j Theta hj
  have hnj := renameInto hn j Theta hj
  have hpj := renameInto hp j Theta hj
  have hsj := renameInto hs j Theta hj
  have hc0j := renameInto hc0 j Theta hj
  have hc1j := renameInto hc1 j Theta hj
  have hc2j := renameInto hc2 j Theta hj
  have hc3j := renameInto hc3 j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hvj hnj hpj hc0j hc1j hc2j hc3j ⊢
  rw [programRename] at hsj
  have hx : (fun i => (![k,head,tau,base,ts,extras] i).relabel j) =
      ![k.relabel j,head.relabel j,tau.relabel j,base.relabel j,ts.relabel j,extras.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun t => Fin.elim0 t)))))) i
  rw [hx] at hsj
  apply (ConcreteHeadMoveLayer.NumberedProof.internalNumbered n arity body beta Theta V
    (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (source.relabel j)
    (k.relabel j) (k.relabel j) (head.relabel j) (head.relabel j) (tau.relabel j) (tau.relabel j)
    (base.relabel j) (base.relabel j) (ts.relabel j) (ts.relabel j) (extras.relabel j) (extras.relabel j)
    encoded encoded (symbols.relabel j) (types.relabel j) (numeral 1) (t0.relabel j)
    (h1.relabel j) (t1.relabel j) (h2.relabel j) (t2.relabel j) (h3.relabel j) (t3.relabel j)
    hvj hnj hpj hsj hsj he he hc0j hc1j hc2j hc3j).mpr
  have rr (x : OTerm beta) : Nonempty (Derivation body Theta (eqn x x)) := ⟨InternalTagArithmeticSupportProof.refl x⟩
  have hm := andIntro (rr (k.relabel j)) (andIntro (rr (tau.relabel j)) (rr (ts.relabel j)))
  obtain ⟨hd⟩ := andIntro (andIntro (rr encoded) (rr (extras.relabel j))) (rr (numeral 1))
  exact andIntro hm ⟨orLeft (orRight hd)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.NumberedProof
