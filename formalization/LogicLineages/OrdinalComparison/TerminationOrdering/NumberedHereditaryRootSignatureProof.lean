module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryRootSignatureProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability
open NumberedHereditaryView NumberedPrimaryConstructorNormalizationProof
open SourceZeroNumberedShapeProof

theorem invariant {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 (hc : SubtypeClosed (fun t => t ∈ S)) {q r : Packed (Fin n) arity Gamma}
 (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
 InUniverse symbols S q.2 → rootSignature symbols S q = rootSignature symbols S r := by
 induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
 case refl => intro _; rfl
 case symm h ih =>
   intro hq
   exact (ih ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mpr hq)).symm
 case trans h k ih ik =>
   intro hq
   exact (ih hq).trans (ik ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mp hq))
 case ordinary f g base target hf hg he ht hp =>
   intro _
   change RootSignature.ordinary (headResult f) _ _ = RootSignature.ordinary (headResult g) _ _
   have hm : (argumentCodes symbols S base : Multiset (Ty × Nat)) = argumentCodes symbols S target :=
     Quot.sound (hp.map (fun p => (p.1,representativeCode symbols S p)))
   rw [he,ht,hm]
 case numbered k f g tau base target types extras hf hg he hp =>
   intro _
   change RootSignature.numbered k tau _ _ _ = RootSignature.numbered k tau _ _ _
   have hm : (argumentCodes symbols S base : Multiset (Ty × Nat)) = argumentCodes symbols S target :=
     Quot.sound (hp.map (fun p => (p.1,representativeCode symbols S p)))
   rw [he,hm]
 case lam q r h ih =>
   intro hq
   exact congrArg (RootSignature.lam _ _) (primaryTypedCode hc ⟨hq.1.2.2,hq.2⟩ h)
 case appFunction q r a h ih =>
   intro hq
   exact congrArg (fun code => RootSignature.app _ _ code (typedCode symbols S ⟨_,a⟩))
     (primaryTypedCode hc ⟨hq.1.2.1,hq.2.1⟩ h)
 case appArgument q a b h ih =>
   intro hq
   exact congrArg (fun code => RootSignature.app _ _ (typedCode symbols S ⟨_,q⟩) code)
     (primaryTypedCode hc ⟨hq.1.2.2,hq.2.2⟩ h)
 case ordinaryArguments f base target h ih =>
   intro hq
   have he := argumentCodesPrimary hc h ⟨hq.1.2,hq.2.2⟩
   exact congrArg (fun codes : List (Ty × Nat) => RootSignature.ordinary _ (RecursiveComparison.headClass f) codes) he
 case numberedBase k f tau base target types extras h ih =>
   intro hq
   have he := argumentCodesPrimary hc h ⟨hq.1.2.1,hq.2.2.1⟩
   exact congrArg (fun codes : List (Ty × Nat) => RootSignature.numbered k tau (RecursiveComparison.headClass f) codes (argumentCodes symbols S extras)) he
 case numberedExtras k f tau base types extras target h ih =>
   intro hq
   exact congrArg (RootSignature.numbered k tau (RecursiveComparison.headClass f) (argumentCodes symbols S base))
     (argumentCodesPrimary hc h ⟨hq.1.2.2,hq.2.2.2⟩)
 all_goals trivial

theorem varComplete {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 {tau upsilon : Ty} (v : Variable Gamma tau) (w : Variable Gamma upsilon)
 (he : rootSignature (arity := arity) symbols S ⟨tau,.var v⟩ = rootSignature symbols S ⟨upsilon,.var w⟩) :
 WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,.var v⟩ ⟨upsilon,.var w⟩ := by
 have h := RootSignature.var.inj he
 cases h.1
 have hn : packedNumber (⟨tau,AuxTerm.var v⟩ : Packed (Fin n) arity Gamma) = packedNumber ⟨tau,.var w⟩ := by
   simp only [packedNumber,NumberedAuxiliaryCoding.termCode,codeNumber,h.2]
 have hp := NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hn
 rw [hp]
 exact .refl _

theorem bottomComplete {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 (tau upsilon : Ty)
 (he : rootSignature (arity := arity) (Gamma := Gamma) symbols S ⟨tau,.bottom tau⟩ = rootSignature symbols S ⟨upsilon,.bottom upsilon⟩) :
 WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,.bottom tau⟩ ⟨upsilon,.bottom upsilon⟩ := by
 have ht := RootSignature.bottom.inj he
 cases ht
 exact .refl _

theorem lambdaComplete {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 (hc : SubtypeClosed (fun t => t ∈ S)) {sigma tau delta upsilon : Ty}
 (q : AuxTerm (Fin n) arity (sigma::Gamma) tau) (r : AuxTerm (Fin n) arity (delta::Gamma) upsilon)
 (hq : InUniverse symbols S (.lam q)) (hr : InUniverse symbols S (.lam r))
 (he : rootSignature symbols S ⟨.arrow sigma tau,.lam q⟩ = rootSignature symbols S ⟨.arrow delta upsilon,.lam r⟩) :
 WindowPrimary (Fin n) arity symbols S Gamma ⟨.arrow sigma tau,.lam q⟩ ⟨.arrow delta upsilon,.lam r⟩ := by
 obtain ⟨hd,ht,hcode⟩ := RootSignature.lam.inj he
 cases hd
 cases ht
 exact .lam q r ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc (sigma::Gamma)
   ⟨tau,q⟩ ⟨tau,r⟩ ⟨hq.1.2.2,hq.2⟩ ⟨hr.1.2.2,hr.2⟩).mp (congrArg Prod.snd hcode))

theorem appComplete {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 (hc : SubtypeClosed (fun t => t ∈ S)) {sigma tau delta upsilon : Ty}
 (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma)
 (g : AuxTerm (Fin n) arity Gamma (.arrow delta upsilon)) (b : AuxTerm (Fin n) arity Gamma delta)
 (hq : InUniverse symbols S (.app f a)) (hr : InUniverse symbols S (.app g b))
 (he : rootSignature symbols S ⟨tau,.app f a⟩ = rootSignature symbols S ⟨upsilon,.app g b⟩) :
 WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,.app f a⟩ ⟨upsilon,.app g b⟩ := by
 obtain ⟨hd,ht,hf,ha⟩ := RootSignature.app.inj he
 cases hd
 cases ht
 have pf := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
   ⟨.arrow sigma tau,f⟩ ⟨.arrow sigma tau,g⟩ ⟨hq.1.2.1,hq.2.1⟩ ⟨hr.1.2.1,hr.2.1⟩).mp (congrArg Prod.snd hf)
 have pa := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
   ⟨sigma,a⟩ ⟨sigma,b⟩ ⟨hq.1.2.2,hq.2.2⟩ ⟨hr.1.2.2,hr.2.2⟩).mp (congrArg Prod.snd ha)
 exact .trans (.appFunction f g a pf) (.appArgument g a b pa)

theorem ordinaryComplete {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 (hc : SubtypeClosed (fun t => t ∈ S)) (f g : Head (Fin n))
 (a : AuxArguments (Fin n) arity Gamma (headArguments arity f)) (b : AuxArguments (Fin n) arity Gamma (headArguments arity g))
 (hq : InUniverse symbols S (.ordinary f a)) (hr : InUniverse symbols S (.ordinary g b))
 (he : rootSignature symbols S ⟨headResult f,.ordinary f a⟩ = rootSignature symbols S ⟨headResult g,.ordinary g b⟩) :
 WindowPrimary (Fin n) arity symbols S Gamma ⟨headResult f,.ordinary f a⟩ ⟨headResult g,.ordinary g b⟩ := by
 obtain ⟨ht,hh,hb⟩ := RootSignature.ordinary.inj he
 exact (NumberedPrimaryConstructorSignaturesProof.ordinaryIff n arity symbols S Gamma hc f g a b hq hr).mpr
   ⟨hh,ht,Quot.exact hb⟩

theorem numberedComplete {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 (hc : SubtypeClosed (fun t => t ∈ S)) (k l : Nat) (f g : Head (Fin n)) (tau upsilon : Ty)
 (a : AuxArguments (Fin n) arity Gamma (headArguments arity f)) (b : AuxArguments (Fin n) arity Gamma (headArguments arity g))
 (types otherTypes : List Ty) (extras : AuxArguments (Fin n) arity Gamma types) (otherExtras : AuxArguments (Fin n) arity Gamma otherTypes)
 (hq : InUniverse symbols S (.numbered k f tau a types extras)) (hr : InUniverse symbols S (.numbered l g upsilon b otherTypes otherExtras))
 (he : rootSignature symbols S ⟨tau,.numbered k f tau a types extras⟩ = rootSignature symbols S ⟨upsilon,.numbered l g upsilon b otherTypes otherExtras⟩) :
 WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,.numbered k f tau a types extras⟩ ⟨upsilon,.numbered l g upsilon b otherTypes otherExtras⟩ := by
 obtain ⟨hk,ht,hh,hb,hex⟩ := RootSignature.numbered.inj he
 exact (NumberedPrimaryConstructorSignaturesProof.numberedIff n arity symbols S Gamma hc k l f g tau upsilon a b types otherTypes extras otherExtras hq hr).mpr
   ⟨hk,ht,hh,Quot.exact hb,hex⟩

theorem complete {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
 (hc : SubtypeClosed (fun t => t ∈ S)) (q r : Packed (Fin n) arity Gamma)
 (hq : InUniverse symbols S q.2) (hr : InUniverse symbols S r.2)
 (he : rootSignature symbols S q = rootSignature symbols S r) :
 WindowPrimary (Fin n) arity symbols S Gamma q r := by
 rcases q with ⟨tau,q⟩
 rcases r with ⟨upsilon,r⟩
 cases q <;> cases r <;> first
 | exact varComplete _ _ he
 | exact bottomComplete _ _ he
 | exact lambdaComplete hc _ _ hq hr he
 | exact appComplete hc _ _ _ _ hq hr he
 | exact ordinaryComplete hc _ _ _ _ hq hr he
 | exact numberedComplete hc _ _ _ _ _ _ _ _ _ _ _ _ hq hr he
 | cases he

theorem exactRootSignature : NumberedHereditaryViewTargets.ExactRootSignature := by
 intro n arity symbols S Gamma hc q r hq hr
 exact ⟨complete hc q r hq hr,fun h => invariant hc h hq⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryRootSignatureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryRootSignatureProof
