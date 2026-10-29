module

public import LogicLineages.Ultrafilters.ConvolutionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_convolution_laws : Targets.ConvolutionLaws := convolution_laws

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
