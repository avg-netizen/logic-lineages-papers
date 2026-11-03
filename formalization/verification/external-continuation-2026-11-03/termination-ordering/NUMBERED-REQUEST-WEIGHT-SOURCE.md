# Actual request expansion decreases structural work

Paper06 lines551–556 motivates effective typed syntax. This component uses the accepted actual typed request expansion without changing it. codeWeight counts one for every Code node, including both function/argument, numbered base/extras, and tuple head/tail occurrences. Binder contexts, head and type metadata do not contribute because expansion passes metadata while removing a Code constructor.

SuccessfulExpansionDecrease requires only actual expand=some children, not validity or an assumed recursive bound. WorklistReplacementDecrease adds the unchanged suffix to both weights. Failed local checks and invalid constructors emit no successful expansion and are discharged from their actual equations.

These are structural decrease facts only. No global evaluator, fuel adequacy, primitive recursion, dependent typed-output presentation, full checker effectivity, arithmetic representability or well-founded ordering claim is made.
