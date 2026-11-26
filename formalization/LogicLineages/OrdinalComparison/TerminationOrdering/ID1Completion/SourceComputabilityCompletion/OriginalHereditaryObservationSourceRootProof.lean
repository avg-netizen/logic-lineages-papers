module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceUniformityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRootUniformityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceRootProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedWindowEquivalence NumberedFiniteUniverse
open OriginalRootObservation OriginalHereditaryObservationSourceUniformityTargets
open OriginalHereditaryObservationRootUniformityProof (sortedPerm)

theorem typedUniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) (hQ : SourceUniform Q n arity symbols S c)
    {Gamma : List Ty} {tau : Ty} (q r : AuxTerm (Fin n) arity Gamma tau)
    (h : WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,q⟩ ⟨tau,r⟩)
    (hq : InUniverse symbols S q) :
    typedValue Q c ⟨tau,q⟩ = typedValue Q c ⟨tau,r⟩ := by
  have hr := (NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S Gamma _ _ h).mp hq
  exact congrArg (Nat.pair (typeNumber tau)) (hQ Gamma ⟨tau,q⟩ ⟨tau,r⟩ hq hr h)

theorem nativeUniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) (hQ : SourceUniform Q n arity symbols S c)
    {Gamma : List Ty} {q r : Packed (Fin n) arity Gamma}
    (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    InUniverse symbols S q.2 → nativeValue Q c q = nativeValue Q c r := by
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types base target _ =>
      NumberedPrimaryConstructorNormalizationProof.GoodArgs symbols S base →
        argumentValues Q c base = argumentValues Q c target)
  case refl => intro _; rfl
  case symm h ih =>
    intro hq
    exact (ih ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mpr hq)).symm
  case trans h k ih ik =>
    intro hq
    exact (ih hq).trans (ik ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mp hq))
  case ordinary f g base target hf hg he ht hp =>
    intro _
    change RecursiveComparison.headClass f = RecursiveComparison.headClass g at he
    have hm := sortedPerm (hp.map (typedValue Q c))
    simp only [nativeValue,argumentValues,he,ht,hm]
  case numbered k f g tau base target types extras hf hg he hp =>
    intro _
    change RecursiveComparison.headClass f = RecursiveComparison.headClass g at he
    have hm := sortedPerm (hp.map (typedValue Q c))
    simp only [nativeValue,argumentValues,he,hm]
  case lam q r h ih =>
    intro hq
    simp only [nativeValue,typedUniform Q n arity symbols S c hQ q r h ⟨hq.1.2.2,hq.2⟩]
  case appFunction q r a h ih =>
    intro hq
    simp only [nativeValue,typedUniform Q n arity symbols S c hQ q r h ⟨hq.1.2.1,hq.2.1⟩]
  case appArgument q a b h ih =>
    intro hq
    simp only [nativeValue,typedUniform Q n arity symbols S c hQ a b h ⟨hq.1.2.2,hq.2.2⟩]
  case ordinaryArguments f base target h ih =>
    intro hq
    simp only [nativeValue,ih ⟨hq.1.2,hq.2.2⟩]
  case numberedBase k f tau base target types extras h ih =>
    intro hq
    simp only [nativeValue,ih ⟨hq.1.2.1,hq.2.2.1⟩]
  case numberedExtras k f tau base types extras target h ih =>
    intro hq
    simp only [nativeValue,ih ⟨hq.1.2.2,hq.2.2.2⟩]
  case nil => rfl
  case cons q r rest target hq hr ihq ihr ha =>
    change typedValue Q c ⟨_,q⟩ :: argumentValues Q c rest = typedValue Q c ⟨_,r⟩ :: argumentValues Q c target
    rw [typedUniform Q n arity symbols S c hQ q r hq ⟨ha.1.1,ha.2.1⟩,ihr ⟨ha.1.2,ha.2.2⟩]

theorem rootPreserves : RootPreserves := by
  intro Q n arity symbols S c hS hQ Gamma q r hq hr h
  rw [OriginalRootObservationNativeProof.nativeCalibration,
    OriginalRootObservationNativeProof.nativeCalibration]
  exact nativeUniform Q n arity symbols S c hQ h hq

theorem calibratedRepresentative : CalibratedRepresentative := by
  intro n arity data hc c ctx hctx hS Gamma q r hq hr h
  rw [OriginalRootObservationActualProof.representativeAtTyped n arity data hc c ctx hctx Gamma q,
    OriginalRootObservationActualProof.representativeAtTyped n arity data hc c ctx hctx Gamma r]
  exact (NumberedLeastCodeRepresentativeProof.representativeEquality n arity ctx.1.1 ctx.1.2 hS Gamma q r hq hr).mpr h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceRootProof
