module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.WindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalAcceptanceBranchProof InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (eqn)

theorem zeroAt (n : Nat) (param ctx rest : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 0) ctx))) :
    Nonempty (Derivation body Delta (graph1 (window n) (numeral 0) param)) := by
  have hc := unaryValue (OriginalDecodedContextValidity.contextGuard n) InternalUnpair.left
    (numeral 0) ctx (Fin.cons param Fin.elim0) hg (pairLeft param ctx rest hp)
  exact zeroBranchIntro (contextCodeGuard n) (InternalAcceptance.constantZero 1)
    (.composition InternalUnpair.left (fun _ : Fin 1 => InternalUnpair.left))
    (numeral 0) (Fin.cons param Fin.elim0) hc
    (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons param Fin.elim0))

theorem positiveAt (n : Nat) (param ctx rest win table : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ctx win table)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) ctx))) :
    Nonempty (Derivation body Delta (graph1 (window n) win param)) := by
  have hc := unaryValue (OriginalDecodedContextValidity.contextGuard n) InternalUnpair.left
    (numeral 1) ctx (Fin.cons param Fin.elim0) hg (pairLeft param ctx rest hp)
  have hv := unaryValue InternalUnpair.left InternalUnpair.left win ctx (Fin.cons param Fin.elim0)
    (pairLeft ctx win table hw) (pairLeft param ctx rest hp)
  exact successorBranchIntro (contextCodeGuard n) (InternalAcceptance.constantZero 1)
    (.composition InternalUnpair.left (fun _ : Fin 1 => InternalUnpair.left))
    win z (Fin.cons param Fin.elim0) hc hv

theorem internalWindow : Targets.InternalWindow := by
  intro n body alpha Delta param ctx rest win table out hp hw
  let A := graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) ctx
  let B := graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 0) ctx
  let R0 := B ⊓ eqn out (numeral 0)
  let R1 := A ⊓ eqn out win
  constructor
  · intro ho
    apply formulaCases A
    · have hg : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hv := positiveAt n param ctx rest win table (withHyp hp A) (withHyp hw A) hg
      have he := valueUnique (window n) out win (Fin.cons param Fin.elim0) (withHyp ho A) hv
      obtain ⟨hr⟩ := andIntro hg he
      exact ⟨InternalQuotientComparisonProof.orRight hr⟩
    · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hg := OriginalTransparentLambdaValidityInternalBranchSupportProof.conjunctionReject
        (.composition (OriginalDecodedWindowValidity.window n) (fun _ : Fin 1 => InternalUnpair.left))
        (.composition (OriginalDecodedContextValidity.tableGuard n) (fun _ : Fin 1 => InternalUnpair.right))
        (Fin.cons ctx Fin.elim0) hn
      have hv := zeroAt n param ctx rest (withHyp hp A.not) hg
      have he := valueUnique (window n) out (numeral 0) (Fin.cons param Fin.elim0) (withHyp ho A.not) hv
      obtain ⟨hr⟩ := andIntro hg he
      exact ⟨InternalQuotientComparisonProof.orLeft hr⟩
  · intro h
    have h0 : Nonempty (Derivation body Delta (R0.imp (graph1 (window n) out param))) := by
      have hr : Nonempty (Derivation body (R0 :: Delta) R0) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hv := zeroAt n param ctx rest (withHyp hp R0) (andLeft hr)
      obtain ⟨he⟩ := andRight hr
      obtain ⟨ho⟩ := outputTransport (window n) (numeral 0) out (Fin.cons param Fin.elim0) ⟨symm he⟩ hv
      exact ⟨Derivation.implicationIntroduction ho⟩
    have h1 : Nonempty (Derivation body Delta (R1.imp (graph1 (window n) out param))) := by
      have hr : Nonempty (Derivation body (R1 :: Delta) R1) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hv := positiveAt n param ctx rest win table (withHyp hp R1) (withHyp hw R1) (andLeft hr)
      obtain ⟨he⟩ := andRight hr
      obtain ⟨ho⟩ := outputTransport (window n) win out (Fin.cons param Fin.elim0) ⟨symm he⟩ hv
      exact ⟨Derivation.implicationIntroduction ho⟩
    obtain ⟨h⟩ := h
    obtain ⟨h0⟩ := h0
    obtain ⟨h1⟩ := h1
    exact ⟨InternalBetaTotalityProof.disjunctionElimination h h0 h1⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.WindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.WindowProof
