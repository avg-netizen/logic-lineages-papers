module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityMembersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExpansionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySupportStatementChecks
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedWindowReduction NumberedWindowEquivalence NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceZeroNumberedComputability SourceConstructorComputability SourceConstructorComputabilityMembersProof
open SourceConstructorComputabilityExpansionProof RankedPrecedenceCertificate
variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

theorem fixed_argumentsC_iff {types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) :
    ArgumentsC context ctx scalar args ↔ ∀ p ∈ argumentList args, TermC context ctx scalar p.2 := by
  exact SourceConstructorComputabilityMembersProof.argumentsC_iff (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (types := types) (args := args)

theorem fixed_argumentsCPerm {xs ys : List Ty}
    {a : AuxArguments (Fin n) arity Gamma xs} {b : AuxArguments (Fin n) arity Gamma ys}
    (hp : (argumentCodes ctx.1.1 ctx.1.2 a).Perm (argumentCodes ctx.1.1 ctx.1.2 b))
    (ha : ArgumentsC context ctx scalar a) : ArgumentsC context ctx scalar b := by
  exact SourceConstructorComputabilityMembersProof.argumentsCPerm (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (xs := xs) (ys := ys) (a := a) (b := b) (hp := hp) (ha := ha)

theorem fixed_argumentsCCons {sigma : Ty} {types : List Ty}
    {q : AuxTerm (Fin n) arity Gamma sigma} {rest : AuxArguments (Fin n) arity Gamma types}
    (hq : TermC context ctx scalar q) (hr : ArgumentsC context ctx scalar rest) :
    ArgumentsC context ctx scalar (.cons q rest) := by
  exact SourceConstructorComputabilityMembersProof.argumentsCCons (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (sigma := sigma) (types := types) (q := q) (rest := rest) (hq := hq) (hr := hr)

theorem fixed_argumentListAppend {xs ys : List Ty}
    (a : AuxArguments (Fin n) arity Gamma xs) (b : AuxArguments (Fin n) arity Gamma ys) :
    argumentList (appendArguments a b) = argumentList a ++ argumentList b := by
  exact SourceConstructorComputabilityMembersProof.argumentListAppend (n := n) (arity := arity) (Gamma := Gamma) (xs := xs) (ys := ys) (a := a) (b := b)

theorem fixed_argumentsCAppend {xs ys : List Ty}
    {a : AuxArguments (Fin n) arity Gamma xs} {b : AuxArguments (Fin n) arity Gamma ys}
    (ha : ArgumentsC context ctx scalar a) (hb : ArgumentsC context ctx scalar b) :
    ArgumentsC context ctx scalar (appendArguments a b) := by
  exact SourceConstructorComputabilityMembersProof.argumentsCAppend (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (xs := xs) (ys := ys) (a := a) (b := b) (ha := ha) (hb := hb)

theorem fixed_argumentsGood {types : List Ty} (args : AuxArguments (Fin n) arity Gamma types)
    (h : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) args) :
    ∀ p ∈ argumentList args, InUniverse ctx.1.1 ctx.1.2 p.2 := by
  exact SourceConstructorComputabilityMembersProof.argumentsGood (n := n) (arity := arity) (Gamma := Gamma) (ctx := ctx) (types := types) (args := args) (h := h)

theorem fixed_argumentsAccessible
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {types : List Ty} {args : AuxArguments (Fin n) arity Gamma types}
    (hm : ArgumentsC context ctx scalar args) : Acc (Descent arity Gamma ctx) (ArgumentValues ctx args) := by
  exact SourceConstructorComputabilityMembersProof.argumentsAccessible (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (types := types) (args := args) (hm := hm)

theorem fixed_argumentStepDescent {types : List Ty} {a b : AuxArguments (Fin n) arity Gamma types}
    (hg : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) a)
    (h : WindowArgumentStep (Fin n) arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma types a b) :
    Descent arity Gamma ctx (ArgumentValues ctx b) (ArgumentValues ctx a) := by
  exact SourceConstructorComputabilityMembersProof.argumentStepDescent (n := n) (arity := arity) (Gamma := Gamma) (ctx := ctx) (types := types) (a := a) (b := b) (hg := hg) (h := h)

theorem fixed_argumentStepComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {types : List Ty} {a b : AuxArguments (Fin n) arity Gamma types}
    (hg : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) a)
    (h : WindowArgumentStep (Fin n) arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma types a b)
    (hm : ArgumentsC context ctx scalar a) : ArgumentsC context ctx scalar b := by
  exact SourceConstructorComputabilityMembersProof.argumentStepComputable (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (types := types) (a := a) (b := b) (hg := hg) (h := h) (hm := hm)

theorem fixed_descentPerm {a b c : List Nat} (hp : a.Perm b)
    (h : Descent arity Gamma ctx c a) : Descent arity Gamma ctx c b := by
  exact SourceConstructorComputabilityMembersProof.descentPerm (arity := arity) (Gamma := Gamma) (ctx := ctx) (a := a) (b := b) (c := c) (hp := hp) (h := h)

theorem fixed_primitiveMultisetComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {source target : List (Packed (Fin n) arity Gamma)}
    (hg : ∀ p ∈ source, InUniverse ctx.1.1 ctx.1.2 p.2)
    (hm : ∀ p ∈ source, TermC context ctx scalar p.2)
    (h : PrimitiveMultiset source target) : ∀ p ∈ target, TermC context ctx scalar p.2 := by
  exact SourceConstructorComputabilityMembersProof.primitiveMultisetComputable (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (source := source) (target := target) (hg := hg) (hm := hm) (h := h)

theorem fixed_primitiveMultisetDescent {xs ys : List Ty}
    {a : AuxArguments (Fin n) arity Gamma xs} {b : AuxArguments (Fin n) arity Gamma ys}
    (hg : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) a)
    (h : PrimitiveMultiset (argumentList a) (argumentList b)) :
    Descent arity Gamma ctx (ArgumentValues ctx b) (ArgumentValues ctx a) := by
  exact SourceConstructorComputabilityMembersProof.primitiveMultisetDescent (n := n) (arity := arity) (Gamma := Gamma) (ctx := ctx) (xs := xs) (ys := ys) (a := a) (b := b) (hg := hg) (h := h)

theorem fixed_neutralFromPrimarySteps
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {tau : Ty} (q : AuxTerm (Fin n) arity Gamma tau)
    (hg : InUniverse ctx.1.1 ctx.1.2 q) (hn : NumberedPrimaryShapes.isLambda q = false)
    (hstep : ∀ p : Packed (Fin n) arity Gamma, InUniverse ctx.1.1 ctx.1.2 p.2 →
      WindowPrimary (Fin n) arity ctx.1.1 ctx.1.2 Gamma ⟨tau,q⟩ p → StepC context ctx scalar p) :
    TermC context ctx scalar q := by
  exact SourceConstructorComputabilityExpansionProof.neutralFromPrimarySteps (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (tau := tau) (q := q) (hg := hg) (hn := hn) (hstep := hstep)

theorem fixed_ordinaryExpansion
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true)
    (f : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (hg : InUniverse ctx.1.1 ctx.1.2 (.ordinary f base)) (hb : ArgumentsC context ctx scalar base)
    (hstep : ∀ (g : Head (Fin n)) (base' : AuxArguments (Fin n) arity Gamma (headArguments arity g)),
      headRank rank g = headRank rank f → (ArgumentValues ctx base').Perm (ArgumentValues ctx base) →
      InUniverse ctx.1.1 ctx.1.2 (.ordinary g base') → ArgumentsC context ctx scalar base' →
      StepC context ctx scalar ⟨headResult g,.ordinary g base'⟩) :
    TermC context ctx scalar (.ordinary f base) := by
  exact SourceConstructorComputabilityExpansionProof.ordinaryExpansion (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (rank := rank) (hrank := hrank) (f := f) (base := base) (hg := hg) (hb := hb) (hstep := hstep)

theorem fixed_numberedExpansion
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true)
    (k : Nat) (f : Head (Fin n)) (tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types)
    (hg : InUniverse ctx.1.1 ctx.1.2 (.numbered k f tau base types extras))
    (hb : ArgumentsC context ctx scalar base) (he : ArgumentsC context ctx scalar extras)
    (hstep : ∀ (g : Head (Fin n)) (base' : AuxArguments (Fin n) arity Gamma (headArguments arity g))
      (types' : List Ty) (extras' : AuxArguments (Fin n) arity Gamma types'),
      headRank rank g = headRank rank f → (ArgumentValues ctx base').Perm (ArgumentValues ctx base) →
      ArgumentValues ctx extras' = ArgumentValues ctx extras →
      InUniverse ctx.1.1 ctx.1.2 (.numbered k g tau base' types' extras') →
      ArgumentsC context ctx scalar base' → ArgumentsC context ctx scalar extras' →
      StepC context ctx scalar ⟨tau,.numbered k g tau base' types' extras'⟩) :
    TermC context ctx scalar (.numbered k f tau base types extras) := by
  exact SourceConstructorComputabilityExpansionProof.numberedExpansion (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (rank := rank) (hrank := hrank) (k := k) (f := f) (tau := tau) (base := base) (types := types) (extras := extras) (hg := hg) (hb := hb) (he := he) (hstep := hstep)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySupportStatementChecks
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySupportStatementChecks
