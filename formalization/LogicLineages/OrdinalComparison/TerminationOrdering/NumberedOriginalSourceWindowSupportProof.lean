module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowSupportProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedOriginalSourceCodec NumberedOriginalSourceWindow
open NumberedOriginalSourceCodecSupportProof Source.SourcePortContexts

theorem groundWindow {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (k : Nat) (args : Fin k → Term Symbol arity Gamma .ground)
    (h : ∀ i,termWindow .ground (termCode (translateOriginal (args i)))=literalTypes (args i)) :
    argumentsWindow (argumentsCode (translateArguments (NumberedOriginalSourceCodec.groundArguments k args)))=
      (List.ofFn (fun i => literalTypes (args i))).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [NumberedOriginalSourceCodec.groundArguments,translateArguments,argumentsCode,argumentsWindow,
      h 0,ih (fun i => args i.succ) (fun i => h i.succ),List.ofFn_succ,List.flatten_cons]

theorem literalWindowCalibration : NumberedOriginalSourceWindowTargets.ActualLiteralWindowCalibration := by
  intro Symbol arity Gamma tau s
  induction s with
  | var v =>
    rename_i sigma
    change sigma.subtypes=sigma.subtypes++[]
    exact (List.append_nil _).symm
  | app f a ihf iha =>
    rw [translateApp]
    simp only [termCode,argumentsCode,termWindow,argumentsWindow,ihf,iha,literalTypes,List.append_nil]
  | lam body ih =>
    rw [translateLam]
    simp only [termCode,termWindow,resultType,literalTypes,ih]
  | zeroC => rfl
  | succC => rfl
  | caseC tau => rfl
  | recC tau => rfl
  | ranked f args ih =>
    rw [translateRanked]
    change Ty.ground.subtypes ++ argumentsWindow
      (argumentsCode (translateArguments (NumberedOriginalSourceCodec.groundArguments (arity f) args)))=
        Ty.ground.subtypes ++ (List.ofFn (fun i => literalTypes (args i))).flatten
    exact congrArg (List.append Ty.ground.subtypes) (groundWindow (arity f) args ih)

theorem requestRecombineCalibration (n : Nat) (request : Request n) :
    recombine request ((requests request).map requestValue)=some (requestValue request) := by
  cases request with
  | inl p => rcases p with ⟨tau,code⟩; cases code <;>
      simp [recombine,rootTypes,requests,requestValue,termWindow,argumentsWindow]
  | inr code => cases code <;>
      simp [recombine,rootTypes,requests,requestValue,termWindow,argumentsWindow]

theorem requestChildCode (n : Nat) (request child : Request n) (h : child ∈ requests request) :
    requestCode child ∈ NumberedSyntaxBoundsPrimrecSupportProof.children (requestCode request) := by
  cases request with
  | inl p =>
    rcases p with ⟨tau,code⟩
    cases code <;> simp [requests] at h
    all_goals first
      | subst child; simp [requestCode,NumberedSyntaxBoundsPrimrecSupportProof.children]
      | rcases h with rfl | rfl <;> simp [requestCode,NumberedSyntaxBoundsPrimrecSupportProof.children]
  | inr code =>
    cases code <;> simp [requests] at h
    rcases h with rfl | rfl <;> simp [requestCode,NumberedSyntaxBoundsPrimrecSupportProof.children]

theorem requestDecrease (n : Nat) (request child : Request n) (h : child ∈ requests request) :
    NumberedLeastCodeRepresentative.codeNumber (requestCode child)<
      NumberedLeastCodeRepresentative.codeNumber (requestCode request) :=
  NumberedSyntaxBoundsPrimrecSupportProof.childrenDecrease n _ _ (requestChildCode n request child h)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowSupportProof
