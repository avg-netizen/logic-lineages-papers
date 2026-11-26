module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildPacketDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalInternalJobAdmissible OriginalInternalJobChildPacket
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def Consumer (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha))
 (H : Program 1) (M W : Program 2) (index role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
 (outRole outType outRaw outGamma outParam annotation : OTerm beta),
 (∀ p ∈ Delta, p.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (Packet H M W (index.relabel j) (role.relabel j) (typ.relabel j)
 (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
 outRole outType outRaw outGamma outParam annotation)) → Nonempty (Derivation body Theta (psi.relabel j))
def ActualCases (first : Bool) (arity : Nat) : Prop := ∀ (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)) →
 Nonempty (Derivation body Delta (graph2 (if first then OriginalHereditaryExpansion.firstJob else OriginalHereditaryExpansion.secondJob) cell raw parameter)) →
 Consumer body Delta H M W (numeral (if first then 0 else 1)) role typ raw cell parameter c gamma psi →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
