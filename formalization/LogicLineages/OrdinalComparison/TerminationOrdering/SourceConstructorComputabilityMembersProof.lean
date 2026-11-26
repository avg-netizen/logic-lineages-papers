module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityMembersProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedWindowReduction NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceZeroNumberedComputability SourceConstructorComputability SourceComputabilityArrowLeastSupportProof

variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

theorem argumentsC_iff {types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) :
    ArgumentsC context ctx scalar args ↔ ∀ p ∈ argumentList args, TermC context ctx scalar p.2 := by
  constructor
  · intro h p hp
    exact h (p.1,representativeCode ctx.1.1 ctx.1.2 p) (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · intro h p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact h q hq

theorem argumentsCPerm {xs ys : List Ty}
    {a : AuxArguments (Fin n) arity Gamma xs} {b : AuxArguments (Fin n) arity Gamma ys}
    (hp : (argumentCodes ctx.1.1 ctx.1.2 a).Perm (argumentCodes ctx.1.1 ctx.1.2 b))
    (ha : ArgumentsC context ctx scalar a) : ArgumentsC context ctx scalar b :=
  fun p h => ha p (hp.mem_iff.mpr h)

theorem argumentsCCons {sigma : Ty} {types : List Ty}
    {q : AuxTerm (Fin n) arity Gamma sigma} {rest : AuxArguments (Fin n) arity Gamma types}
    (hq : TermC context ctx scalar q) (hr : ArgumentsC context ctx scalar rest) :
    ArgumentsC context ctx scalar (.cons q rest) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hq
  · exact hr p hp

theorem argumentListAppend {xs ys : List Ty}
    (a : AuxArguments (Fin n) arity Gamma xs) (b : AuxArguments (Fin n) arity Gamma ys) :
    argumentList (appendArguments a b) = argumentList a ++ argumentList b := by
  induction xs with
  | nil => cases a; rfl
  | cons sigma xs ih => cases a with
    | cons q rest => exact congrArg (List.cons ⟨sigma,q⟩) (ih rest)

theorem argumentsCAppend {xs ys : List Ty}
    {a : AuxArguments (Fin n) arity Gamma xs} {b : AuxArguments (Fin n) arity Gamma ys}
    (ha : ArgumentsC context ctx scalar a) (hb : ArgumentsC context ctx scalar b) :
    ArgumentsC context ctx scalar (appendArguments a b) := by
  apply (argumentsC_iff _).mpr
  intro p hp
  rw [argumentListAppend] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (argumentsC_iff a).mp ha p hp
  · exact (argumentsC_iff b).mp hb p hp

theorem argumentsGood {types : List Ty} (args : AuxArguments (Fin n) arity Gamma types)
    (h : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) args) :
    ∀ p ∈ argumentList args, InUniverse ctx.1.1 ctx.1.2 p.2 :=
  (NumberedUniverseOperationsProof.actualArgumentOccurrences (Fin n) arity _ _ Gamma types args).mp h

theorem argumentsAccessible
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {types : List Ty} {args : AuxArguments (Fin n) arity Gamma types}
    (hm : ArgumentsC context ctx scalar args) : Acc (Descent arity Gamma ctx) (ArgumentValues ctx args) := by
  apply SourceDirectAccessibilityProof.actualListAccessibility n arity Gamma ctx
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  exact SourceZeroNumberedAccessibilitySupportProof.quotientAccessible n arity Gamma context ctx hc p.2
    (SourceComputabilityLeastProof.actualComputabilityAccessible n arity Gamma context ctx scalar
      hc hclosed hcal p.1 p.2 (hm p hp))

theorem argumentStepDescent {types : List Ty} {a b : AuxArguments (Fin n) arity Gamma types}
    (hg : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) a)
    (h : WindowArgumentStep (Fin n) arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma types a b) :
    Descent arity Gamma ctx (ArgumentValues ctx b) (ArgumentValues ctx a) :=
  SourceZeroNumberedAccessibilitySupportProof.replacementDirect
    (SourceZeroNumberedReplacementProof.argumentStepReplacement h hg)

theorem argumentStepComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {types : List Ty} {a b : AuxArguments (Fin n) arity Gamma types}
    (hg : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) a)
    (h : WindowArgumentStep (Fin n) arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma types a b)
    (hm : ArgumentsC context ctx scalar a) : ArgumentsC context ctx scalar b := by
  apply SourceZeroNumberedAccessibilitySupportProof.replacementPreservesMembers
    (CodeC n arity Gamma context scalar) _
    (SourceZeroNumberedReplacementProof.argumentStepReplacement h hg) hm
  intro sigma x y hcx hxy
  exact SourceComputabilityDownwardProof.actualComputabilityDownward n arity Gamma context ctx scalar
    hc hclosed hcal sigma x y hcx ((relationCalibration n arity Gamma context ctx hc x y).mpr (.step hxy))

theorem descentPerm {a b c : List Nat} (hp : a.Perm b)
    (h : Descent arity Gamma ctx c a) : Descent arity Gamma ctx c b := by
  exact (DirectMultisetPresentationProof.permutationInvariance Nat _ a c b c hp (List.Perm.refl c)).mp h

theorem primitiveMultisetComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {source target : List (Packed (Fin n) arity Gamma)}
    (hg : ∀ p ∈ source, InUniverse ctx.1.1 ctx.1.2 p.2)
    (hm : ∀ p ∈ source, TermC context ctx scalar p.2)
    (h : PrimitiveMultiset source target) : ∀ p ∈ target, TermC context ctx scalar p.2 := by
  obtain ⟨kept,removed,inserted,hs,ht,hn,hi⟩ := h
  intro p hp
  rcases List.mem_append.mp (ht.mem_iff.mp hp) with hp | hp
  · exact hm p (hs.mem_iff.mpr (List.mem_append_left _ hp))
  · obtain ⟨q,hq,hmark⟩ := hi p hp
    have hmem := hs.mem_iff.mpr (List.mem_append_right kept hq)
    have hpath := SourcePrimitiveMultisetQuotientProof.primitiveMarkQuotient
      (above := NumberedCopyCertificate.tableAbove ctx.2) (hg q hmem) hmark
    have hcq := hm q hmem
    cases hmark with
    | mk k q r he =>
      exact SourceComputabilityDownwardProof.actualComputabilityDownward n arity Gamma context ctx scalar
        hc hclosed hcal _ (representativeCode ctx.1.1 ctx.1.2 ⟨_,q⟩)
        (representativeCode ctx.1.1 ctx.1.2 ⟨_,r⟩) hcq
        ((relationCalibration n arity Gamma context ctx hc _ _).mpr hpath)

theorem primitiveMultisetDescent {xs ys : List Ty}
    {a : AuxArguments (Fin n) arity Gamma xs} {b : AuxArguments (Fin n) arity Gamma ys}
    (hg : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) a)
    (h : PrimitiveMultiset (argumentList a) (argumentList b)) :
    Descent arity Gamma ctx (ArgumentValues ctx b) (ArgumentValues ctx a) := by
  have hd := SourcePrimitiveMultisetQuotientProof.actualPrimitiveMultisetQuotientDescent
    n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma
    (argumentList a) (argumentList b) (argumentsGood a hg) h
  simpa only [Descent,DirectMultisetAccessibility.ReverseDirect,
    QuotientDominationCertificates.relation,ArgumentValues,argumentCodes,List.map_map,Function.comp_def] using hd
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityMembersProof
