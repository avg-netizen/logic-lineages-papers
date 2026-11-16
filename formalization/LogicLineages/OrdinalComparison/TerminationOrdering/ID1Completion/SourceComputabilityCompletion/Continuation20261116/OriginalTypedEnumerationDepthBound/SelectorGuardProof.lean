module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SelectorGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (valueUnique)
open InternalControlGraphSupportProof (headTransport)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem transfer (n : Nat) (q : Program 1) (raw observed child : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph1 q observed raw)))
    (hc : Nonempty (Derivation body Delta (graph1 q child raw)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) observed))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)) :=
  headTransport (OriginalCodeValidityGuard.check n) (suc z) observed child Fin.elim0
    (valueUnique q observed child ![raw] ho hc) hg

theorem lambdaCode (n : Nat) (raw metadata child first : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)) :=
  transfer n (firstOf (.projection 0)) raw first child hf
    (andLeft (andRight (lambdaFields raw z metadata child hc))) hg

theorem ordinary (n : Nat) (raw metadata child first : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw metadata child)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)) :=
  transfer n (firstOf (.projection 0)) raw first child hf
    (andLeft (andRight (ordinaryFields raw z metadata child hc))) hg

theorem application (n : Nat) (raw typ left right first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw typ left right)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) second))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)) := by
  have hfields := applicationFields raw typ left right hc
  exact ⟨transfer n (firstOf (.projection 0)) raw first left hf (andLeft (andRight hfields)) hlg,
    transfer n (secondOf (.projection 0)) raw second right hs (andRight (andRight hfields)) hrg⟩

theorem cons (n : Nat) (raw typ left right first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ left right)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) second))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)) := by
  have hfields := consFields raw typ left right hc
  exact ⟨transfer n (firstOf (.projection 0)) raw first left hf (andLeft (andRight hfields)) hlg,
    transfer n (secondOf (.projection 0)) raw second right hs (andRight (andRight hfields)) hrg⟩

theorem numbered (n : Nat) (raw label head typ left types right first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,left,types,right])))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) second))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)) := by
  have hfields := numberedFields raw label head typ left types right hc
  exact ⟨transfer n (firstOf (.projection 0)) raw first left hf (andLeft (andRight hfields)) hlg,
    transfer n (secondOf (.projection 0)) raw second right hs (andRight (andRight hfields)) hrg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SelectorGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SelectorGuardProof
