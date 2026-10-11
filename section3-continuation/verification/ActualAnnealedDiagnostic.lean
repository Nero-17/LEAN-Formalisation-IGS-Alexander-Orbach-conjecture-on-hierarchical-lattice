import IGSIII34.Spectral.Collars.ActualSameMasterAllClocks
theorem diagnostic : True := by
  run_tac do
    discard <| liftM (do IO.println "DIAG_ENTRY"; (← IO.getStdout).flush).toBaseIO
  trivial
