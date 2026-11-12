module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionParentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalParserSupportProof (selectorPair)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def windowSelector : Program 1 := leftOf (rightOf (.projection 0))

theorem fromPairs (child raw parameter window gamma : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma))) :
 Nonempty (Derivation body Delta (graph1 windowSelector window child)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons child Fin.elim0
 exact unaryValue InternalUnpair.left (rightOf (.projection 0)) window parameter xs
   (pairLeft parameter window gamma hp)
   (unaryValue InternalUnpair.right (.projection 0) parameter child xs
     (pairRight child raw parameter hc) (projectionValue 0 xs))

theorem parameterWindow (raw parameter window gamma output : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (ho : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstParameter output raw parameter))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left window output)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 apply programCases (leftOf (.projection 0) : Program 2) xs _
 intro beta rho Theta tag hrho ht
 let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at ht
 simp only [graph1Rename]
 have hp' := renameInto hp rho Theta hrho
 have ho' := renameInto ho rho Theta hrho
 simp only [graph2Rename] at hp' ho'
 apply numeralBranchCases (leftOf (.projection 0)) (.projection 1) _ tag 1
   (output.relabel rho) xx _ ht ho'
 · intro Xi hi hno
   have he := valueUnique (.projection 1 : Program 2) (output.relabel rho) (parameter.relabel rho) xx hno (projectionValue 1 xx)
   exact headTransport InternalUnpair.left (window.relabel rho) (parameter.relabel rho) (output.relabel rho) Fin.elim0
     (by exact ⟨InternalTagArithmeticSupportProof.symm (Classical.choice he)⟩)
     (pairLeft (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) (weakenProof hp' hi))
 · intro Xi hi _ hyes
   exact pairOfLeft (leftOf (.projection 1)) _ (output.relabel rho) (window.relabel rho) xx hyes
     (unaryValue InternalUnpair.left (.projection 1) (window.relabel rho) (parameter.relabel rho) xx
       (pairLeft (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) (weakenProof hp' hi)) (projectionValue 1 xx))

theorem jobWindow {n : Nat} (p q : Program n) (child parameter window : OTerm alpha)
 (xs : Fin n → OTerm alpha)
 (hc : Nonempty (Derivation body Delta (programGraph (pairOf p q) child xs)))
 (hq : Nonempty (Derivation body Delta (programGraph q parameter xs)))
 (hw : Nonempty (Derivation body Delta (graph1 InternalUnpair.left window parameter))) :
 Nonempty (Derivation body Delta (graph1 windowSelector window child)) := by
 let xx : Fin 1 → OTerm alpha := Fin.cons child Fin.elim0
 exact unaryValue InternalUnpair.left (rightOf (.projection 0)) window parameter xx hw
   (unaryValue InternalUnpair.right (.projection 0) parameter child xx
     (pairOfRight p q child parameter xs hc hq) (projectionValue 0 xx))

theorem firstWindow (raw parameter window gamma child : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob child raw parameter))) :
 Nonempty (Derivation body Delta (graph1 windowSelector window child)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 apply programCases OriginalHereditaryExpansion.firstParameter xs _
 intro beta rho Theta output hrho hq
 let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 simp only [graph1Rename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hp' hc'
 exact jobWindow _ OriginalHereditaryExpansion.firstParameter (child.relabel rho) output (window.relabel rho) xx hc' hq
   (parameterWindow (raw.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) output hp' hq)

theorem secondWindow (raw parameter window gamma child : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob child raw parameter))) :
 Nonempty (Derivation body Delta (graph1 windowSelector window child)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 exact jobWindow _ (.projection 1) child parameter window xs hc (projectionValue 1 xs) (pairLeft parameter window gamma hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextSupportProof
