module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationUniformityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRootUniformityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedWindowEquivalence
open OriginalRootObservation OriginalHereditaryObservationUniformityTargets

theorem sortedPerm {xs ys : List Nat} (h : xs.Perm ys) :
    xs.insertionSort (· ≤ ·) = ys.insertionSort (· ≤ ·) := by
  have he : (xs : Multiset Nat) = ys := Multiset.coe_eq_coe.mpr h
  have hs := congrArg (Multiset.sort (· ≤ ·)) he
  simpa only [Multiset.coe_sort,List.mergeSort_eq_insertionSort] using hs

theorem typedUniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) (hQ : Uniform Q n arity symbols S c)
    {Gamma : List Ty} {tau : Ty} (q r : AuxTerm (Fin n) arity Gamma tau)
    (h : WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,q⟩ ⟨tau,r⟩) :
    typedValue Q c ⟨tau,q⟩ = typedValue Q c ⟨tau,r⟩ :=
  congrArg (Nat.pair (typeNumber tau)) (hQ Gamma ⟨tau,q⟩ ⟨tau,r⟩ h)

theorem nativeUniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) (hQ : Uniform Q n arity symbols S c)
    {Gamma : List Ty} {q r : Packed (Fin n) arity Gamma}
    (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    nativeValue Q c q = nativeValue Q c r := by
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types base target _ => argumentValues Q c base = argumentValues Q c target)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h k ih ik => exact ih.trans ik
  case ordinary f g base target hf hg he ht hp =>
    have hm := sortedPerm (hp.map (typedValue Q c))
    simp only [nativeValue,argumentValues,he,ht,hm]
  case numbered k f g tau base target types extras hf hg he hp =>
    have hm := sortedPerm (hp.map (typedValue Q c))
    simp only [nativeValue,argumentValues,he,hm]
  case lam q r h ih =>
    simp only [nativeValue,typedUniform Q n arity symbols S c hQ q r h]
  case appFunction q r a h ih =>
    simp only [nativeValue,typedUniform Q n arity symbols S c hQ q r h]
  case appArgument q a b h ih =>
    simp only [nativeValue,typedUniform Q n arity symbols S c hQ a b h]
  case ordinaryArguments f base target h ih => simp only [nativeValue,ih]
  case numberedBase k f tau base target types extras h ih => simp only [nativeValue,ih]
  case numberedExtras k f tau base types extras target h ih => simp only [nativeValue,ih]
  case nil => rfl
  case cons q r rest target hq hr ihq ihr =>
    change typedValue Q c ⟨_,q⟩ :: argumentValues Q c rest = typedValue Q c ⟨_,r⟩ :: argumentValues Q c target
    rw [typedUniform Q n arity symbols S c hQ q r hq,ihr]

theorem rootPreserves : RootPreserves := by
  intro Q n arity symbols S c hQ Gamma q r h
  rw [OriginalRootObservationNativeProof.nativeCalibration,
    OriginalRootObservationNativeProof.nativeCalibration]
  exact nativeUniform Q n arity symbols S c hQ h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRootUniformityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRootUniformityProof
