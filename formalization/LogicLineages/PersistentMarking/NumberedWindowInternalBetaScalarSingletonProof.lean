module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaSingletonProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaScalarSingletonProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate singletonInputs)
open NumberedWindowInternalSparseAddressSingletonChecks (exact_OpenInstalledSingleton)
open NumberedWindowInternalBetaSub (betaChecker)
open NumberedWindowInternalBetaRootDispatch (root')

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- On the freshly installed unrefined body, turn the same literal β root
witness into the exact scalar one-hop certificate. The actual endpoint
address, context, type, raw and least reports are held in that very body. -/
theorem accepted (i j cv tv syn : Program 1) (original other windowProg least d : Program 3)
    (guard arg body sub : Program 2) (c : Nat) (left right ctx ty src dst q r : OTerm α) :
    let raw := typedRaw5 (root' original (betaChecker guard arg body sub)) other windowProg syn
    let R := addressPositive cv tv raw least
    let B := sourceBody (data i j R d) c
    let w := rootWitnessTerm (rawCons (numeral 6) z)
    Nonempty (Derivation B Γ (addressReport left ctx ty src)) →
    Nonempty (Derivation B Γ (addressReport right ctx ty dst)) →
    Nonempty (Derivation B Γ (unary cv (suc z) ctx)) →
    Nonempty (Derivation B Γ (unary tv (suc z) ty)) →
    Nonempty (Derivation B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r])) →
    Nonempty (Derivation B Γ (programGraph least (suc src) ![ctx,ty,q])) →
    Nonempty (Derivation B Γ (programGraph least (suc dst) ![ctx,ty,r])) →
    Nonempty (Derivation B Γ (accepts R left (singletonCertificate dst q w r) right)) := by
  intro raw R B w hL hR hC hT hRaw hl hr
  obtain ⟨leftG⟩ := hL
  obtain ⟨rightG⟩ := hR
  obtain ⟨ctxG⟩ := hC
  obtain ⟨tyG⟩ := hT
  obtain ⟨rawG⟩ := hRaw
  obtain ⟨first⟩ := hl
  obtain ⟨last⟩ := hr
  have calls : Derivation B Γ (actualCalls raw least ctx ty src dst q w r) :=
    Derivation.conjunctionIntroduction rawG (Derivation.conjunctionIntroduction first last)
  have inputs : Nonempty (Derivation B Γ (singletonInputs cv tv raw least left right ctx ty src dst q w r)) :=
    ⟨Derivation.conjunctionIntroduction leftG (Derivation.conjunctionIntroduction rightG
      (Derivation.conjunctionIntroduction ctxG (Derivation.conjunctionIntroduction tyG calls)))⟩
  exact closedApply (exact_OpenInstalledSingleton i j cv tv d raw least c α left right ctx ty src dst q w r) inputs

#print axioms accepted
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaScalarSingletonProof
