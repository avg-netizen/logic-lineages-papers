module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource.BundleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem unpack {arity k : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld a : Program 1) (baseX : Program 3) (tag : Nat)
 (he : (nodes p)[tag]? = some ⟨6,extra f lhs rhs t rawOld a baseX⟩) :
 let old := selectedOld rawOld
 let Q : Program 1 → Program 1 → Program 3 → Program 5 :=
  fun old a baseX => CumulativePropositionalSource.verifier f lhs rhs old a baseX
 (∃ (etag : Nat), (nodes p)[etag]? =
  some ⟨6,CurrentStructuralProducerSource.extendedExtra f lhs rhs t Q old a baseX⟩) ∧
 (∀ item ∈ items rawOld, ∃ (itag : Nat), (nodes p)[itag]? = some item) := by
 dsimp only
 let Q : Program 1 → Program 1 → Program 3 → Program 5 :=
  fun old a baseX => CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let head : Packed := ⟨6,CurrentStructuralProducerSource.extendedExtra f lhs rhs t Q (selectedOld rawOld) a baseX⟩
 have hall := ReflexivityInstalled.BundleProof.bundleInstallation (head :: items rawOld) arity p tag he
 refine ⟨hall head List.mem_cons_self,?_⟩
 intro item hi
 exact hall item (List.mem_cons_of_mem _ hi)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource.BundleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource.BundleProof
