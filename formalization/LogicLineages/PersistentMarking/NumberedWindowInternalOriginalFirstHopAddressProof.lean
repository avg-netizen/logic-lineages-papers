module

public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopTailProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopAddressProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalAccessibilityRules (edge certificate)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalParameterizedAddressPositive (exact_OriginalAddressAt)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport witnessData)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportsCases addressReportRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt headData)
open NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (headCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalNeutralFactsTargets (direct firstHop)
open NumberedWindowInternalOriginalFirstHopCoreProof
open NumberedWindowInternalOriginalFirstHopTailProof

abbrev R (cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  addressPositive cv tv raw least

abbrev hop (cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  oneHopProgram (R cv tv raw least)

abbrev S (i cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  literalData i (R cv tv raw least)

private theorem mkAddress {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (x cert y ctx ty src dst : OTerm α)
    (a : D B Γ (addressReport x ctx ty src)) (b : D B Γ (addressReport y ctx ty dst))
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (fold : D B Γ (positiveAt raw least ctx ty src cert dst)) :
    D B Γ (programGraph (R cv tv raw least) (suc z) ![x,cert,y]) := by
  change D B Γ (programGraph (addressPositive cv tv raw least) (suc z) ![x,cert,y])
  rw [← exact_OriginalAddressAt]
  exact exact_OriginalAddressAtIntro cv tv (positive raw least) x cert y ctx ty src dst a b gc gt fold

private theorem literalDirect {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (i cv tv : Program 1) (raw : Program 5) (least : Program 3) (c : Nat)
    (x hd y ctx ty src dst : OTerm α)
    (a : D B Γ (addressReport x ctx ty src)) (b : D B Γ (addressReport y ctx ty dst))
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (known : D B Γ (selectedGraph raw least (suc dst) ctx ty (suc src) hd)) :
    D B Γ (direct (S i cv tv raw least) (hop cv tv raw least) c x y) := by
  let r := R cv tv raw least
  let h := hop cv tv raw least
  have one := exact_OriginalPositiveOneCell raw least ctx ty src hd dst known
  have full := mkAddress cv tv raw least x (rawCons hd z) y ctx ty src dst a b gc gt one
  have call := exact_OneHopProgramIntro r x hd y full
  have cert := (exact_CertificateRules i (jRaw i) h (dCore i r permutation) false c B α Γ x y hd).2 call
  exact edgeIntroduction cert

private theorem continuation {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (i cv tv : Program 1) (raw : Program 5) (least : Program 3) (c : Nat)
    (x y ctx ty src dst hd tl next : OTerm α)
    (a : D B Γ (addressReport x ctx ty src)) (b : D B Γ (addressReport y ctx ty dst))
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (one : D B Γ (selectedGraph raw least (suc next) ctx ty (suc src) hd))
    (tail : D B Γ (finishAt raw least ctx ty next tl dst)) :
    D B Γ (firstHop (S i cv tv raw least) (hop cv tv raw least) c x y) := by
  let r := R cv tv raw least
  let s := S i cv tv raw least
  let h := hop cv tv raw least
  let empty := eqn tl z
  have add {F : Formula α} (C : Formula α) (p : D B Γ F) : D B (C::Γ) F :=
    p.map (Derivation.weakening (fun _ m => List.mem_cons_of_mem _ m))
  have atEnd : D B (empty::Γ) (firstHop s h c x y) := by
    have same := exact_PositiveHeadNilEndpoint raw least ctx ty next tl dst (add empty tail)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have exactY : D B (empty::Γ) (selectedGraph raw least (suc dst) ctx ty (suc src) hd) :=
      outputTransport (advance raw least) (suc next) (suc dst) ![ctx,ty,suc src,hd] same (add empty one)
    exact provideFirstHop s h c x y y
      (literalDirect i cv tv raw least c x hd y ctx ty src dst (add empty a) (add empty b)
        (add empty gc) (add empty gt) exactY)
      (restLeft ⟨refl y⟩)
  have after : D B (empty.not::Γ) (firstHop s h c x y) := by
    let mid := literalAddress ctx ty next
    have midReport := exact_OriginalLiteralAddressReport (B := B) (Γ := empty.not::Γ) ctx ty next
    have single := literalDirect i cv tv raw least c x hd mid ctx ty src next (add empty.not a)
      midReport (add empty.not gc) (add empty.not gt) (add empty.not one)
    have folding := exact_PositiveHeadContinues raw least ctx ty next tl dst (add empty.not tail)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have graph := mkAddress cv tv raw least mid tl y ctx ty next dst midReport (add empty.not b)
      (add empty.not gc) (add empty.not gt) folding
    have cert := (exact_CertificateRules i (jRaw i) r (dCore i r permutation) false c B α
      (empty.not::Γ) mid y tl).2 graph
    exact provideFirstHop s h c x mid y single (restRight (edgeIntroduction cert))
  obtain ⟨atEnd⟩ := atEnd
  obtain ⟨after⟩ := after
  exact ⟨disjunctionElimination (excludedMiddle empty) (Derivation.implicationIntroduction atEnd)
    (Derivation.implicationIntroduction after)⟩

/-- Physical ordinary address acceptance supplies an actual one-cell
hop on the original fields and a zero-or-positive remainder. The
intermediate address is the original literal packed context, type and
selected least. The original certified arguments are unchanged. -/
theorem exact_OrdinaryFirstHopGraph (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (c : Nat) {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (x cert y : OTerm α)
    (held : D B Γ (programGraph (R cv tv raw least) (suc z) ![x,cert,y])) :
    D B Γ (firstHop (S i cv tv raw least) (hop cv tv raw least) c x y) := by
  let s := S i cv tv raw least
  let h := hop cv tv raw least
  have accepted := NumberedWindowInternalSparseAddressPositiveOpenForwardProof.forward
    cv tv raw least x cert y held
  apply reportsCases cv tv raw least x cert y _ accepted
  intro β j Δ ctx ty src dst _ reports
  rw [firstHopRename]
  obtain ⟨row⟩ := reports
  let X := x.relabel j
  let Y := y.relabel j
  let w := cert.relabel j
  have a : D B Δ (addressReport X ctx ty src) := ⟨Derivation.conjunctionLeft row⟩
  have b : D B Δ (addressReport Y ctx ty dst) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight row)⟩
  have rest := Derivation.conjunctionRight (Derivation.conjunctionRight row)
  have gc : D B Δ (unary cv (suc z) ctx) := ⟨Derivation.conjunctionLeft rest⟩
  have gt : D B Δ (unary tv (suc z) ty) := ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight rest)⟩
  have full : D B Δ (positiveAt raw least ctx ty src w dst) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight rest)⟩
  have opened := NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof.forward raw least ctx ty src w dst full
  apply headCases raw least ctx ty src w dst (firstHop s h c X Y) opened
  intro γ k Ω hd tl next keep fields
  rw [firstHopRename]
  have aa := renameInto a k Ω keep
  have bb := renameInto b k Ω keep
  have cc := renameInto gc k Ω keep
  have tt := renameInto gt k Ω keep
  simp only [addressReportRename] at aa bb
  simp only [unaryRename,sucRelabel,zRelabel] at cc tt
  obtain ⟨decoded⟩ := fields
  have suffix := Derivation.conjunctionRight decoded
  exact continuation i cv tv raw least c (X.relabel k) (Y.relabel k) (ctx.relabel k) (ty.relabel k)
    (src.relabel k) (dst.relabel k) hd tl next aa bb cc tt
    ⟨Derivation.conjunctionLeft suffix⟩ ⟨Derivation.conjunctionRight suffix⟩

/-- Discharge the ground proof's exact first-hop input for the ordinary
selected literal presentation, including existential path certificates. -/
theorem exact_OrdinaryFirstHop (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α) :
    let s := S i cv tv raw least
    let h := hop cv tv raw least
    D (sourceBody s c) Γ (edge s false c x y) →
    D (sourceBody s c) Γ (firstHop s h c x y) := by
  dsimp only
  intro accepted
  let s := S i cv tv raw least
  let h := hop cv tv raw least
  let r := R cv tv raw least
  let B := sourceBody s c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := certificate s false c (x.relabel j) (y.relabel j) w
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have selected := (exact_CertificateRules i (jRaw i) r (dCore i r permutation) false c B _ Δ
    (x.relabel j) (y.relabel j) w).1 ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨split⟩ := exact_OrdinaryFirstHopGraph i cv tv raw least c (x.relabel j) w (y.relabel j) selected
  have whole : Derivation B Δ (weaken (firstHop s h c x y)) := by
    rw [weaken,firstHopRename]
    exact split
  obtain ⟨e⟩ := accepted
  rw [edgeExists] at e
  exact ⟨Derivation.existentialElimination e whole⟩

#print axioms exact_OrdinaryFirstHopGraph
#print axioms exact_OrdinaryFirstHop
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopAddressProof
