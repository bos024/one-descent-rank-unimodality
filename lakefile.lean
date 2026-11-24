import Lake
open Lake DSL

package OneDescentReproducibility

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib PaperProofs where
  srcDir := "formal"
  roots := #[`DepthSlackArmIdentities, `DepthSlackTransport]

lean_lib FiniteCertificates where
  srcDir := "reproducibility/reduction"
  roots := #[
    `ActualDyadicSlopeNorm,
    `ActualDyadicSourcePayment,
    `CoupledSourceWindowA2,
    `FirstMissingTwelveCriticalCertificate,
    `FirstMissingTwelveCriticalPart00,
    `FirstMissingTwelveCriticalPart01,
    `FirstMissingTwelveCriticalPart02,
    `FirstMissingTwelveCriticalPart03,
    `FirstMissingTwelveCriticalPart04,
    `FirstMissingTwelveCriticalPart05,
    `FirstMissingTwelveCriticalPart06,
    `FirstMissingTwelveCriticalPart07,
    `FirstMissingTwelveCriticalPart08,
    `FirstMissingTwelveCriticalPart09,
    `FirstMissingTwelveCriticalPart10,
    `FirstMissingTwelveCriticalPart11,
    `FirstMissingTwelveCriticalPart12,
    `FirstMissingTwelveCriticalPart13,
    `FirstMissingTwelveCriticalPart14,
    `FirstMissingTwelveCriticalPart15,
    `FirstMissingTwelveCriticalPart16,
    `FirstMissingTwelveCriticalPart17,
    `FirstMissingTwelveCriticalPart18,
    `FirstMissingTwelveCriticalPart19,
    `FirstMissingTwelveCriticalPart20,
    `FirstMissingTwelveCriticalPart21,
    `FirstMissingTwelveCriticalPart22,
    `FirstMissingTwelveCriticalPart23,
    `FirstMissingTwelveCriticalPart24,
    `FirstMissingTwelveCriticalPart25,
    `FirstMissingTwelveCriticalPart26,
    `FirstMissingTwelveCriticalPart27,
    `FirstMissingTwelveCriticalPart28,
    `FirstMissingTwelveCriticalPart29,
    `FirstMissingTwelveCriticalPart30,
    `FirstMissingTwelveHeadGuards,
    `FixedTerminalElevenDensity,
    `FixedTerminalFourteenSlope
  ]
