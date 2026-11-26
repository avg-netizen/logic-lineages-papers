module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.InputCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.SeedInputProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeSpecialization
theorem certificateCongruence {arity ctx : Nat} (p : Program arity) (mtag ctag atag qtag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) :
 ∀ n (f : Formula n) (a b : List.Vector (Term ctx) n) (antecedent : Term ctx),
 (∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (b.get i)))) →
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.certificate mtag ctag atag qtag f a antecedent)
   (PrescribedRuntimeSpecialization.certificate mtag ctag atag qtag f b antecedent))) := by
 intro n
 induction n with
 | zero =>
  intro f a b ant h
  exact ⟨.logical (.reflexive _)⟩
 | succ n ih =>
  intro f a b ant h
  let T := GorbowPRNumeralCalculation.Theory p
  have ht : ∀ i, Nonempty (Derivation T (.equal (a.tail.get i) (b.tail.get i))) := by
   intro i
   set_option pp.all true in
    simpa only [T, List.Vector.get_tail_succ] using h i.succ
  have hh : Nonempty (Derivation T (.equal a.head b.head)) := by
   simpa only [List.Vector.get_zero] using h 0
  obtain ⟨hh⟩ := hh
  obtain ⟨hA⟩ := InputCongruenceProof.formula p ctag atag hc ha (headEnvironment n) a.tail b.tail ht f
  obtain ⟨hbody⟩ := InputCongruenceProof.formula p ctag atag hc ha
   (UniformRuntimeEnvironmentAgreement.specialize (headEnvironment n))
   (a.head ::ᵥ a.tail) (b.head ::ᵥ b.tail)
   (fun i => by
    cases i using Fin.cases with
    | zero => exact ⟨hh⟩
    | succ i => exact ht i) f
  have hline := HistoryAppend.PositiveProof.binaryCongruence qtag _ _ _ _ hA hh
  have himp := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hline (.logical (.reflexive _))
  obtain ⟨hant⟩ := ih (.all f) a.tail b.tail ant ht
  have hout := Logic.callCongruence T mtag
   ((.zero : Term ctx) ::ᵥ UniformRuntimeSpecializationStep.body ctag atag (headEnvironment n) f a.tail a.head ::ᵥ
    UniformClosedRule13Certificate.certificate ctag qtag (formulaValue ctag atag a.tail f (headEnvironment n)) a.head ::ᵥ
    PrescribedRuntimeSpecialization.certificate mtag ctag atag qtag (.all f) a.tail ant ::ᵥ nil)
   ((.zero : Term ctx) ::ᵥ UniformRuntimeSpecializationStep.body ctag atag (headEnvironment n) f b.tail b.head ::ᵥ
    UniformClosedRule13Certificate.certificate ctag qtag (formulaValue ctag atag b.tail f (headEnvironment n)) b.head ::ᵥ
    PrescribedRuntimeSpecialization.certificate mtag ctag atag qtag (.all f) b.tail ant ::ᵥ nil)
   (fun i => by
    cases i using Fin.cases with
    | zero => exact .logical (.reflexive _)
    | succ i => cases i using Fin.cases with
      | zero => exact hbody
      | succ i => cases i using Fin.cases with
        | zero => exact himp
        | succ i => cases i using Fin.cases with
          | zero => exact hant
          | succ i => exact Fin.elim0 i)
  exact ⟨hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.SeedInputProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.SeedInputProof
